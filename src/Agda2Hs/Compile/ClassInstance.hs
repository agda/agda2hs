module Agda2Hs.Compile.ClassInstance where

import Control.Arrow ( (>>>), (***), (&&&), first, second )
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Generics ( mkT, everywhere, listify, extT, everything, mkQ, Data )
import Data.List
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Maybe
import Data.Map ( Map )
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps

import Agda.Syntax.Common hiding ( Ranged )
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding ( withCurrentModule )

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Lens
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Function
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

compileInstance :: Definition -> C (Hs.Decl ())
compileInstance def = setCurrentRange (nameBindingSite $ qnameName $ defName def) $ do
  ir <- compileInstRule [] (unEl . defType $ def)
  locals <- takeWhile (isAnonymousModuleName . qnameModule . fst)
          . dropWhile ((<= defName def) . fst)
          . sortDefs <$> liftTCM curDefs
  (ds, rs) <- concatUnzip <$> mapM (compileInstanceClause locals) funClauses
  when (length (nub rs) > 1) $
    genericDocError =<< fsep (pwords "More than one minimal record used.")
  return $ Hs.InstDecl () Nothing ir (Just ds)
  where Function{..} = theDef def

compileInstRule :: [Hs.Asst ()] -> Term -> C (Hs.InstRule ())
compileInstRule cs ty = case unSpine1 ty of
  Def f es | Just args <- allApplyElims es -> do
    vs <- mapM (compileType . unArg) $ filter keepArg args
    f <- hsQName f
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
    DomType t  -> __IMPOSSIBLE__
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
etaExpandClause cl@Clause{clauseBody = Nothing} = genericError "Instance definition with absurd pattern!"
etaExpandClause cl@Clause{namedClausePats = ps, clauseBody = Just t} = do
  case t of
    Con c _ _ -> do
      let fields = conFields c
      let cls = [ cl{ namedClausePats = ps ++ [unnamed . ProjP ProjSystem <$> f],
                      clauseBody      = Just $ t `applyE` [Proj ProjSystem $ unArg f] }
                | f <- fields ]
      return cls
    _ ->
      genericDocError =<< fsep (pwords $ "Type class instances must be defined using copatterns (or top-level" ++
                                         " records) and cannot be defined using helper functions.")

compileInstanceClause :: LocalDecls -> Clause -> C ([Hs.InstDecl ()], [QName])
compileInstanceClause ls c = do
  -- abuse compileClause:
  -- 1. drop any patterns before record projection to suppress the instance arg
  -- 2. use record proj. as function name
  -- 3. process remaing patterns as usual

  -- TODO: check that the things we drop here are not doing any matching
  case dropWhile (isNothing . isProjP) (namedClausePats c) of
    [] ->
      concatUnzip <$> (mapM (compileInstanceClause ls) =<< etaExpandClause c)
    p : ps -> do
      let c' = c {namedClausePats = ps}
          ProjP _ q = namedArg p

      -- We want the actual field name, not the instance-opened projection.
      (q, _, _) <- origProjection q
      arg <- fieldArgInfo q
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
        , f .~ q
        -> do d <- chaseDef n
              fc <- drop 1 <$> compileFun d
              let hd = hsName $ prettyShow $ nameConcrete $ qnameName $ defName d
              let fc' = dropPatterns 1 $ replaceName hd uf fc
              return (map (Hs.InsDecl ()) fc', [n])

         -- Projection of a default implementation: drop while making sure these are drawn from the
         -- same (minimal) dictionary as the primitive fields.
         | Clause {namedClausePats = [], clauseBody = Just (Def n es)} <- c'
         , n .~ q
         , Just [ Def n' _ ] <- map unArg . filter keepArg <$> allApplyElims es
         -> do n' <- resolveExtendedLambda n'
               return ([], [n'])

         -- No minimal dictionary used, proceed with compiling as a regular clause.
         | otherwise
         -> do (_ , x) <- compileClause ls uf c'
               return ([Hs.InsDecl () (Hs.FunBind () [x])], [])

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
      isField f _ = (`elem` fields) . unQual <$> hsQName f
  findDefinitions isField modName

classMemberNames :: Definition -> C [Hs.Name ()]
classMemberNames def =
  case theDef def of
    Record{recFields = fs} -> fmap unQual <$> traverse hsQName (map unDom fs)
    _ -> genericDocError =<< text "Not a record:" <+> prettyTCM (defName def)
