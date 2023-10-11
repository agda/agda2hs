module Agda2Hs.Compile.ClassInstance where

import Control.Monad ( when, filterM, unless )
import Control.Monad.Reader ( local )

import Data.Foldable ( toList )
import Data.List ( nub )
import Data.Maybe ( isNothing, mapMaybe )
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts.Syntax as Hs
import Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common ( curDefs, sortDefs )

import Agda.Interaction.BasicOps ( parseName )

import Agda.Syntax.Common hiding ( Ranged )
import Agda.Syntax.Internal
import Agda.Syntax.Position ( noRange )
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad ( resolveName )
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute ( Apply(applyE) )
import Agda.TypeChecking.Records

import Agda.Utils.Lens
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Function
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

enableCopatterns :: C a -> C a
enableCopatterns = local $ \e -> e { copatternsEnabled = True }

disableCopatterns :: C a -> C a
disableCopatterns = local $ \e -> e { copatternsEnabled = False }

enableStrategies :: Maybe (Hs.DerivStrategy ()) -> C ()
enableStrategies Nothing = return ()
enableStrategies (Just s) = do
  tellExtension Hs.DerivingStrategies
  enableStrategy s

enableStrategy :: Hs.DerivStrategy () -> C ()
enableStrategy (Hs.DerivStock ())    = return () -- is included in GHC
enableStrategy (Hs.DerivAnyclass ()) = tellExtension Hs.DeriveAnyClass -- since 7.10.1
enableStrategy (Hs.DerivNewtype ())  = tellExtension Hs.GeneralizedNewtypeDeriving -- since 6.8.1.
enableStrategy (Hs.DerivVia () t)    = tellExtension Hs.DerivingVia -- since 8.6.1

compileInstance :: InstanceTarget -> Definition -> C (Hs.Decl ())
compileInstance (ToDerivation strategy) def@Defn{..} =
  setCurrentRangeQ defName $ do
    tellExtension Hs.StandaloneDeriving
    enableStrategies strategy
    ir <- compileInstRule [] (unEl defType)
    return $ Hs.DerivDecl () strategy Nothing ir
compileInstance ToDefinition def@Defn{..} =
  enableCopatterns $ setCurrentRangeQ defName $ do
    ir <- compileInstRule [] (unEl defType)
    withFunctionLocals defName $ do
      (ds, rs) <- concatUnzip
              <$> mapM (compileInstanceClause (qnameModule defName)) funClauses
      when (length (nub rs) > 1) $
        genericDocError =<< fsep (pwords "More than one minimal record used.")
      return $ Hs.InstDecl () Nothing ir (Just ds)
    where Function{..} = theDef

compileInstRule :: [Hs.Asst ()] -> Term -> C (Hs.InstRule ())
compileInstRule cs ty = case unSpine1 ty of
  Def f es | Just args <- allApplyElims es -> do
    vs <- mapM (compileType . unArg) $ filter keepArg args
    f <- compileQName f
    return $
      Hs.IRule () Nothing (ctx cs) $ foldl (Hs.IHApp ()) (Hs.IHCon () f) (map pars vs)
    where ctx [] = Nothing
          ctx cs = Just (Hs.CxTuple () cs)
          -- put parens around anything except a var or a constant
          pars :: Hs.Type () -> Hs.Type ()
          pars t@(Hs.TyVar () _) = t
          pars t@(Hs.TyCon () _) = t
          pars t = Hs.TyParen () t
  Pi a b -> compileDom (absName b) a >>= \case
    DomDropped -> underAbstr a b (compileInstRule cs . unEl)
    DomConstraint hsA ->
      underAbstraction a b (compileInstRule (cs ++ [hsA]) . unEl)
    DomType _ t -> __IMPOSSIBLE__
  _ -> __IMPOSSIBLE__

-- Plan:
--  - ✓ Eta-expand if no copatterns (top-level)
--  - ✓ drop default implementations and chase definitions of primitive methods in minimal records + *checks*
--  - ✓ compileInstanceClause on resulting clauses
--
-- *checks*
--  - ✓ Only one minimal record
--  - ✓ all primitives of the minimal are projected from the same dictionary
--  - ✓ default implementation that get dropped are also projected from that same dictionary

etaExpandClause :: Clause -> C [Clause]
etaExpandClause cl@Clause{clauseBody = Nothing} =
  genericError "Instance definition with absurd pattern!"
etaExpandClause cl@Clause{namedClausePats = ps, clauseBody = Just t} = do
  case t of
    Con c _ _ -> do
      let fields = conFields c
      let cls = [ cl{ namedClausePats = ps ++ [unnamed . ProjP ProjSystem <$> f],
                      clauseBody      = Just $ t `applyE` [Proj ProjSystem $ unArg f] }
                | f <- fields ]
      return cls
    _ -> genericDocError =<< fsep (pwords $
      "Type class instances must be defined using copatterns (or top-level" ++
      " records) and cannot be defined using helper functions.")

compileInstanceClause :: ModuleName -> Clause -> C ([Hs.InstDecl ()], [QName])
compileInstanceClause curModule c = withClauseLocals curModule c $ do
  -- abuse compileClause:
  -- 1. drop any patterns before record projection to suppress the instance arg
  -- 2. use record proj. as function name
  -- 3. process remaing patterns as usual

  -- TODO: check that the things we drop here are not doing any matching
  case dropWhile (isNothing . isProjP) (namedClausePats c) of
    [] ->
      concatUnzip <$> (mapM (compileInstanceClause curModule) =<< etaExpandClause c)
    p : ps -> do
      let c' = c {namedClausePats = ps}
          ProjP _ q = namedArg p

      -- We want the actual field name, not the instance-opened projection.
      (q, _, _) <- origProjection q
      arg <- fieldArgInfo q

      reportSDoc "agda2hs.compile.instance" 15 $
        text "Compiling instance clause for" <+> prettyTCM (Arg arg $ Def q [])

      let uf = hsName $ prettyShow $ nameConcrete $ qnameName q

      let
        (.~) :: QName -> QName -> Bool
        x .~ y = nameConcrete (qnameName x) == nameConcrete (qnameName y)

        resolveExtendedLambda :: QName -> C QName
        resolveExtendedLambda n | isExtendedLambdaName n = defName <$> getConstInfo n
                                | otherwise              = return n

        chaseDef :: QName -> C Definition
        chaseDef n = do
          d <- getConstInfo n
          let Function {..} = theDef d
          case funClauses of
            [ Clause {clauseBody = Just (Def n' [])} ] -> do
              chaseDef n'
            _ -> return d

      if
        | isInstance arg, usableModality arg -> do
            unless (null ps) $ genericDocError =<< text "not allowed: explicitly giving superclass"
            body <- case clauseBody c' of
              Nothing -> genericDocError =<< text "not allowed: absurd clause for superclass"
              Just b  -> return b
            addContext (clauseTel c') $ checkInstance body
            return ([], [])
        | not (keepArg arg) -> return ([], [])
        -- Projection of a primitive field: chase down definition and inline as instance clause.
        | Clause {namedClausePats = [], clauseBody = Just (Def n es)} <- c'
        , [(_, f)] <- mapMaybe isProjElim es
        , f .~ q -> do
          reportSDoc "agda2hs.compile.instance" 20 $
            text "Instance clause is projected from" <+> prettyTCM (Def n [])
          reportSDoc "agda2hs.compile.instance" 20 $
            text $ "raw projection:" ++ prettyShow (Def n [])
          d <- chaseDef n
          fc <- compileFun False d
          let hd = hsName $ prettyShow $ nameConcrete $ qnameName $ defName d
          let fc' = dropPatterns 1 $ replaceName hd uf fc
          return (map (Hs.InsDecl ()) fc', [n])

         -- Projection of a default implementation: drop while making sure these are drawn from the
         -- same (minimal) dictionary as the primitive fields.
        | Clause {namedClausePats = [], clauseBody = Just (Def n es)} <- c'
        , n .~ q -> do
          case map unArg . filter keepArg <$> allApplyElims es of
            Just [ Def f _ ] -> do
              reportSDoc "agda2hs.compile.instance" 20 $ vcat
                  [ text "Dropping default instance clause" <+> prettyTCM c'
                  , text "with minimal dictionary" <+> prettyTCM f
                  ]
              reportSDoc "agda2hs.compile.instance" 40 $
                  text $ "raw dictionary:" ++ prettyShow f
              return ([], [f])
            _ -> genericDocError =<< text "illegal instance declaration: instances using default methods should use a named definition or an anonymous `λ where`."

        -- No minimal dictionary used, proceed with compiling as a regular clause.
        | otherwise -> do
          reportSDoc "agda2hs.compile.instance" 20 $ text "Compiling instance clause" <+> prettyTCM c'
          ms <- disableCopatterns $ compileClause curModule uf c'
          return ([Hs.InsDecl () (Hs.FunBind () (toList ms))], [])

fieldArgInfo :: QName -> C ArgInfo
fieldArgInfo f = do
  r <- maybe badness return =<< liftTCM (getRecordOfField f)
  Record{ recFields = fs } <- theDef <$> getConstInfo r
  case filter ((== f) . unDom) fs of
    df : _ -> return $ getArgInfo df
    []     -> badness
  where
    badness = genericDocError =<< text "Not a record field:" <+> prettyTCM f

findDefinitions :: (QName -> Definition -> C Bool) -> ModuleName -> C [Definition]
findDefinitions p m = do
  localDefs    <- (^. sigDefinitions) <$> (^. stSignature) <$> getTCState
  importedDefs <- (^. sigDefinitions) <$> (^. stImports)   <$> getTCState
  let allDefs = HMap.union localDefs importedDefs
      inMod = [ (x, def) | (x, def) <- HMap.toList allDefs, isInModule x m ]
  map snd <$> filterM (uncurry p) inMod

resolveStringName :: String -> C QName
resolveStringName s = do
  cqname <- liftTCM $ parseName noRange s
  rname <- liftTCM $ resolveName cqname
  case rname of
    DefinedName _ aname _ -> return $ anameName aname
    _ -> genericDocError =<< text ("Couldn't find " ++ s)

lookupDefaultImplementations :: QName -> [Hs.Name ()] -> C [Definition]
lookupDefaultImplementations recName fields = do
  let modName = qnameToMName recName
      isField f _ = (`elem` fields) . unQual <$> compileQName f
  findDefinitions isField modName

classMemberNames :: Definition -> C [Hs.Name ()]
classMemberNames def =
  case theDef def of
    Record{recFields = fs} -> fmap unQual <$> traverse compileQName (map unDom fs)
    _ -> genericDocError =<< text "Not a record:" <+> prettyTCM (defName def)
