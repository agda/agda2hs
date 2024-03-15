module Agda2Hs.Compile.ClassInstance where

import Control.Monad ( when, filterM, unless )
import Control.Monad.Reader ( local )

import Data.Foldable ( toList )
import Data.List ( nub )
import Data.Maybe ( isNothing, mapMaybe )
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts as Hs
import Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common ( curDefs, sortDefs )

import Agda.Interaction.BasicOps ( parseName )

import Agda.Syntax.Common hiding ( Ranged )
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern ( patternToTerm )
import Agda.Syntax.Position ( noRange )
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad ( resolveName )
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute ( Apply(applyE), absBody, absApp )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Telescope ( mustBePi )

import Agda.Utils.Lens
import Agda.Utils.Monad ( ifNotM )
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


-- | Enable the approriate extensions for a given Haskell deriving strategy.
enableStrategy :: Maybe (Hs.DerivStrategy ()) -> C ()
enableStrategy Nothing = return ()
enableStrategy (Just s) = do
  tellExtension Hs.DerivingStrategies
  case s of
    Hs.DerivStock ()    -> return () -- is included in GHC
    Hs.DerivAnyclass () -> tellExtension Hs.DeriveAnyClass -- since 7.10.1
    Hs.DerivNewtype ()  -> tellExtension Hs.GeneralizedNewtypeDeriving -- since 6.8.1.
    Hs.DerivVia () t    -> tellExtension Hs.DerivingVia -- since 8.6.1


compileInstance :: InstanceTarget -> Definition -> C (Hs.Decl ())

compileInstance (ToDerivation strategy) def@Defn{..} =
  setCurrentRangeQ defName $ do
    tellExtension Hs.StandaloneDeriving
    enableStrategy strategy
    ir <- compileInstRule [] (unEl defType)
    return $ Hs.DerivDecl () strategy Nothing ir

compileInstance ToDefinition def@Defn{..} =
  enableCopatterns $ setCurrentRangeQ defName $ do
    ir <- compileInstRule [] (unEl defType)
    withFunctionLocals defName $ do
      reportSDoc "agda2hs.compile.instance" 20 $ vcat $
        text "compileInstance clauses: " :
        map (nest 2 . prettyTCM) funClauses
      (ds, rs) <- concatUnzip
              <$> mapM (compileInstanceClause (qnameModule defName) defType) funClauses
      reportSDoc "agda2hs.compile.instance" 20 $ vcat $
        text "compileInstance compiled clauses: " :
        map (nest 2 . text . pp) ds
      when (length (nub rs) > 1) $
        genericDocError =<< fsep (pwords "More than one minimal record used.")
      return $ Hs.InstDecl () Nothing ir (Just ds)
    where Function{..} = theDef


compileInstRule :: [Hs.Asst ()] -> Term -> C (Hs.InstRule ())
compileInstRule cs ty = case unSpine1 ty of
  Def f es | Just args <- allApplyElims es -> do
    fty <- defType <$> getConstInfo f
    vs <- compileTypeArgs fty args
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
  Pi a b -> compileDomType (absName b) a >>= \case
    DomDropped -> underAbstr a b (compileInstRule cs . unEl)
    DomConstraint hsA ->
      underAbstraction a b (compileInstRule (cs ++ [hsA]) . unEl)
    DomType _ t -> __IMPOSSIBLE__
    DomForall _ -> __IMPOSSIBLE__
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


compileInstanceClause :: ModuleName -> Type -> Clause -> C ([Hs.InstDecl ()], [QName])
compileInstanceClause curModule ty c = ifNotM (keepClause c) (return ([], [])) $ do

  let naps = namedClausePats c

  -- there are no projection patterns: we need to eta-expand the clause
  if all (isNothing . isProjP) naps then do
    cs <- etaExpandClause c
    reportSDoc "agda2hs.compile.instance" 20 $ vcat $
      text "compileInstance expanded clauses: " :
      map (nest 2 . prettyTCM) cs
    concatUnzip <$> mapM (compileInstanceClause curModule ty) cs

  -- otherwise we seek the first projection pattern
  else addContext (KeepNames $ clauseTel c) $
    withClauseLocals curModule c $ compileInstanceClause' curModule ty naps c { clauseTel = EmptyTel }

-- abuse compileClause:
-- 1. drop any patterns before record projection to suppress the instance arg
-- 2. use record proj. as function name
-- 3. process remaing patterns as usual
compileInstanceClause' :: ModuleName -> Type -> NAPs -> Clause -> C ([Hs.InstDecl ()], [QName])
compileInstanceClause' curModule ty [] c = __IMPOSSIBLE__
compileInstanceClause' curModule ty (p:ps) c

  -- reached record projection
  | ProjP _ q <- namedArg p = do

    -- we put back the remaining patterns in the original clause 
    let c' = c {namedClausePats = ps}

    -- We want the actual field name, not the instance-opened projection.
    (q, _, _) <- origProjection q
    arg <- fieldArgInfo q

    -- retrieve the type of the projection
    Just (unEl -> Pi a b) <- getDefType q ty
    -- We don't really have the information available to reconstruct the instance
    -- head. However, all dependencies on the instance head are in erased positions, 
    -- so we can just use a dummy term instead
    let instanceHead = __DUMMY_TERM__ 
        ty' = b `absApp` instanceHead

    reportSDoc "agda2hs.compile.instance" 15 $
      text "Compiling instance clause for" <+> prettyTCM (Arg arg $ Def q [])

    reportSDoc "agda2hs.compile.instance" 15 $
      text "Clause type: " <+> prettyTCM ty'

    reportSDoc "agda2hs.compile.instance" 15 $
      text "Clause patterns:" <+> prettyTCM (namedArg <$> ps)

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
      -- Instance field: check canonicity.
      | isInstance arg -> do
          unless (null ps) $ genericDocError =<< text "not allowed: explicitly giving superclass"
          body <- case clauseBody c' of
            Nothing -> genericDocError =<< text "not allowed: absurd clause for superclass"
            Just b  -> return b
          checkInstance body
          reportSDoc "agda2hs.compile.instance" 20 $ vcat
            [ text "compileInstanceClause dropping clause"
            , nest 2 $ prettyTCM c
            ]
          return ([], [])

      -- Projection of a primitive field: chase down definition and inline as instance clause.
      | Clause {namedClausePats = [], clauseBody = Just (Def n es)} <- c'
      , [(_, f)] <- mapMaybe isProjElim es
      , f .~ q -> do
        reportSDoc "agda2hs.compile.instance" 20 $
          text "Instance clause is projected from" <+> prettyTCM (Def n [])
        reportSDoc "agda2hs.compile.instance" 20 $
          text $ "raw projection:" ++ prettyShow (Def n [])
        d <- chaseDef n
        fc <- compileLocal $ compileFun False d
        let hd = hsName $ prettyShow $ nameConcrete $ qnameName $ defName d
        let fc' = {- dropPatterns 1 $ -} replaceName hd uf fc
        reportSDoc "agda2hs.compile.instance" 6 $ vcat $
          text "compileInstanceClause compiled clause: " :
          map (nest 2 . text . pp) fc'
        return (map (Hs.InsDecl ()) fc', [n])

       -- Projection of a default implementation: drop while making sure these are drawn from the
       -- same (minimal) dictionary as the primitive fields.
      | Clause {namedClausePats = [], clauseBody = Just (Def n es)} <- c'
      , n .~ q -> do
        let err = genericDocError =<< text "illegal instance declaration: instances using default methods should use a named definition or an anonymous `λ where`."
            filterArgs :: Type -> [Term] -> C [Term]
            filterArgs ty [] = return []
            filterArgs ty (v:vs) = do
              reportSDoc "agda2hs.compile.instance" 25 $ text "filterArgs: v =" <+> prettyTCM v
              (a,b) <- mustBePi ty
              reportSDoc "agda2hs.compile.instance" 25 $ text "filterArgs: a =" <+> prettyTCM a
              let rest = underAbstraction a b $ \b' -> filterArgs b' vs
              compileDom a >>= \case
                DODropped -> rest
                DOType -> rest
                DOTerm -> (v:) <$> rest
                DOInstance -> err
        ty <- defType <$> getConstInfo n
        traverse (filterArgs ty) (map unArg <$> allApplyElims es) >>= \case
          Just [ Def f _ ] -> do
            reportSDoc "agda2hs.compile.instance" 20 $ vcat
                [ text "Dropping default instance clause" <+> prettyTCM c'
                , text "with minimal dictionary" <+> prettyTCM f
                ]
            reportSDoc "agda2hs.compile.instance" 40 $
                text $ "raw dictionary:" ++ prettyShow f
            return ([], [f])
          _ -> err

      -- No minimal dictionary used, proceed with compiling as a regular clause.
      | otherwise -> do
        reportSDoc "agda2hs.compile.instance" 20 $ text "Compiling instance clause" <+> prettyTCM c'
        ms <- disableCopatterns $ compileClause curModule Nothing uf ty' c'
        let cc = Hs.FunBind () (toList ms)
        reportSDoc "agda2hs.compile.instance" 20 $ vcat
          [ text "compileInstanceClause compiled clause"
          , nest 2 $ text $ pp cc
          ]
        return ([Hs.InsDecl () cc], [])

-- finding a pattern other than a projection: we skip
-- NOTE(flupe): actually I think we may want to throw hard errors here
--              if there is something other than erased parameters
compileInstanceClause' curModule ty (p:ps) c = do
  (a, b) <- mustBePi ty
  compileInstanceClause' curModule (absApp b (patternToTerm $ namedArg p)) ps c

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
  localDefs    <- (^. sigDefinitions) . (^. stSignature) <$> getTCState
  importedDefs <- (^. sigDefinitions) . (^. stImports)   <$> getTCState
  let allDefs = HMap.union localDefs importedDefs
      inMod = [ (x, def) | (x, def) <- HMap.toList allDefs, isInModule x m ]
  map snd <$> filterM (uncurry p) inMod


resolveStringName :: String -> C QName
resolveStringName s = do
  cqname <- liftTCM $ parseName noRange s
  rname  <- liftTCM $ resolveName cqname
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
