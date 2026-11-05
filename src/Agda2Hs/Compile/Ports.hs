-- Compiling (im|ex)ports
module Agda2Hs.Compile.Ports ( compilePorts, preludeImportDecl, hasHaskellReexports ) where

import Data.Char ( isUpper )
import Data.Functor.Compose ( Compose(Compose) )
import qualified Data.List as L
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( validVarId, validConId, pp )

import Agda.Compiler.Backend
import Agda.TypeChecking.Pretty ( pretty, text, prettyList_, (<+>) )
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Scope.Base
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Utils.Monad ( liftM2, filterM, anyM, foldM )
import Agda.Utils.Impossible
import qualified Agda.Utils.List1 as List1

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils

--------------------------------------------------------------------------------
-- main

compilePorts
  :: String -> ModuleEnv -> Imports -> Exports -> TCM ([Hs.ImportDecl ()], Hs.ExportSpecList ())
compilePorts top menv is0 es0 = do
  reexps <- extractReexports menv

  let is = filter ((top /=) . Hs.prettyPrint . importModule) (map toImport reexps ++ is0)
  checkClashingImports is
  let imps = Map.toList $ groupImports is
  reportSLn "agda2hs.import" 10 $ "All imported modules: " ++ show (map (pp . fst . fst) imps)
  let impDecls = map (uncurry $ uncurry makeImportDecl) imps

  let exps = map compileExport (map toExport reexps ++ es0)
  -- TODO: check clashing exports
  reportSDoc "agda2hs.export" 10 $
    "All exports: " <+> prettyList_ (map (text . pp) exps)

  return (impDecls, Hs.ExportSpecList () exps)

-- | Generate a prelude import considering prelude config options (hiding, implicit, etc).
preludeImportDecl :: PreludeOptions -> Hs.ImportDecl ()
preludeImportDecl (PreludeOpts{..}) =
  let toName s | validVarId s || validConId s = Hs.Ident () s
      toName s = Hs.Symbol () s

      -- if the prelude is implicit, we use the provided hiding list.
      -- if it is explicit, we use the import list.
      spec = Hs.ImportSpecList () preludeImplicit $
              map (Hs.IVar () . toName) $
                if preludeImplicit then preludeHiding
                                   else concat preludeImports
  in Hs.ImportDecl
    { importAnn       = ()
    , importModule    = Hs.prelude_mod ()
    , importQualified = False
    , importSrc       = False
    , importSafe      = False
    , importPkg       = Nothing
    , importAs        = Nothing
    , importSpecs     = Just spec
    }

--------------------------------------------------------------------------------
-- extract re-exports

reexportedNames :: Scope -> Set QName
reexportedNames =
  foldMap (Set.singleton . anameName) . Compose . namesInScope [ImportedNS]

hasHaskellReexports :: TopLevelModuleName -> TCM Bool
hasHaskellReexports mname = do
  iface <- maybe __IMPOSSIBLE__ miInterface <$> getVisitedModule mname
  anyM shouldBeExported $ reexportedNames $ currentScope $ iInsideScope iface

data Reexport
  = ReexportModule (Hs.ModuleName ())

type Reexports = [Reexport]

toImport :: Reexport -> Import
toImport = \case
  ReexportModule m -> ImportModule m

toExport :: Reexport -> Export
toExport = \case
  ReexportModule m -> ExportModule m

extractReexports :: ModuleEnv -> TCM Reexports
extractReexports menv = do
  topInfo <- moduleAbstrSyn menv
  let currScope = currentScope $ topLevelScope topInfo
  reexps <- groupByTopLevelModule $ reexportedNames currScope
  reexpsHs <- traverse (filterSetA shouldBeExported) reexps
  reexpDecls <- topLevelReexportDecls topInfo
  let reexpDeclsHs = Map.intersectionWith (,) reexpsHs reexpDecls
  reportSDoc "agda2hs.reexport" 40 $ "reexported names:" <+> pretty reexps
  reportSDoc "agda2hs.reexport" 40 $ "reexported names exist in Haskell:" <+> pretty reexpsHs
  reportSDoc "agda2hs.reexport" 40 $ "all reexport declarations:" <+> pretty reexpDecls
  reportSDoc "agda2hs.reexport" 20 $ "reexport declarations to compile:" <+> pretty reexpDeclsHs
  flip Map.foldMapWithKey reexpDeclsHs $ \mod (names, directives) -> do
    (kind, mod') <- compileTopLevelModuleName mod
    case directives of
      [ImportDirective {using = UseEverything, hiding = []}] ->
        case kind of
          AgdaModule
            | Set.null names -> pure []
            | otherwise -> pure [ReexportModule mod']
          HsModule -> pure [ReexportModule mod']
          PrimModule
            | prettyShow mod == "Haskell.Prelude" -> pure [ReexportModule mod']
            | otherwise -> pure []
      -- TODO(satoshi): support 'using' and 'hiding'
      _ -> pure []
  where
    -- TODO(satoshi): use Set.filterA when we start using containers>=0.8.1
    filterSetA :: Applicative m => (a -> m Bool) -> Set.Set a -> m (Set.Set a)
    filterSetA p = fmap Set.fromDistinctAscList .  filterM p . List1.toList . Set.toAscList

-- | Collect top-level reexport declarations.
-- A module can be reexported multiple times with different directives hence the list.
topLevelReexportDecls :: TopLevelInfo -> TCM (Map TopLevelModuleName [A.ImportDirective])
topLevelReexportDecls = collect Map.empty . insideDecls . topLevelDecls
  where
    -- top-level declarations starts with a bunch of imports then the top-level module of the file
    -- ignore "outside" imports because those can't be reexports
    insideDecls = \case
      [A.Section _ _ _ _ decls] -> decls
      (_ : decls) -> insideDecls decls

    collect = foldM $ \acc decl -> case decl of
      A.Import _ modName impDir@(ImportDirective{publicOpen = Just _}) -> do
        modName <- getTopLevelModuleForModuleName modName
        pure $! Map.insertWith (++) modName [impDir] acc
      A.ScopedDecl _ decls -> collect acc decls
      _ -> pure acc

--------------------------------------------------------------------------------
-- compile imports

type ImportSpecMap = Map NamespacedName (Set (Hs.Name ()))
type ImportDeclMap = Map (Hs.ModuleName (), Qualifier) (Maybe ImportSpecMap)

checkClashingImports :: Imports -> TCM ()
checkClashingImports [] = return ()
checkClashingImports (Import mod as p (NamespacedName _ q) : is) =
  case filter isClashing is of
    (i : _) -> agda2hsStringError $ mkErrorMsg i
    []      -> checkClashingImports is
  where
    isClashing (Import _ as' p' (NamespacedName _ q')) =
      (as' == as) && (p' /= p) && (q' == q) && not (bareWithSelfParent p p')
      where
        -- An unnamed record constructor is imported under the record
        -- name, which is also the name of the constructor itself
        -- (e.g. @Example(Example)@). Importing it together with the bare
        -- record name is not a clash: both refer to the same entity.
        bareWithSelfParent Nothing  (Just p) = nnName p == q
        bareWithSelfParent (Just p) Nothing  = nnName p == q
        bareWithSelfParent _        _        = False
    isClashing ImportInstances{} = False
    mkErrorMsg (Import _ _ p' (NamespacedName _ q')) =
          "Clashing import: " ++ pp q ++ " (both from "
      ++ prettyShow (pp . nnName <$> p) ++ " and "
      ++ prettyShow (pp . nnName <$> p') ++ ")"
    -- TODO: no range information as we only have Haskell names at this point
checkClashingImports (ImportInstances mod : is) = checkClashingImports is
checkClashingImports (ImportModule mod : is) = checkClashingImports is

groupImports :: Imports -> ImportDeclMap
groupImports = flip foldr Map.empty $ \case
  (Import mod as parent name) ->
    Map.insertWith mergeChildren (mod,as) (makeSingle parent name)
  (ImportInstances mod) ->
    Map.insertWith mergeChildren (mod,Unqualified) (Just mempty)
  (ImportModule mod) ->
    Map.insertWith mergeChildren (mod,Unqualified) Nothing
  where
    mergeChildren :: Maybe ImportSpecMap -> Maybe ImportSpecMap -> Maybe ImportSpecMap
    mergeChildren = liftM2 (Map.unionWith Set.union)

    makeSingle :: Maybe NamespacedName -> NamespacedName -> Maybe ImportSpecMap
    makeSingle Nothing  q = Just $ Map.singleton q Set.empty
    makeSingle (Just p) q = Just $ Map.singleton p $ Set.singleton (nnName q)

-- TODO: avoid having to do this by having a CName instead of a
-- Name in the Import datatype
makeCName :: Hs.Name () -> Hs.CName ()
makeCName n@(Hs.Ident _ s)
  | Just True == (isUpper . fst <$> L.uncons s) = Hs.ConName () n
  | otherwise        = Hs.VarName () n
makeCName n@(Hs.Symbol _ s)
  | (fst <$> L.uncons s) == Just ':' = Hs.ConName () n
  | otherwise     = Hs.VarName () n

makeImportSpec :: NamespacedName -> Set (Hs.Name ()) -> Hs.ImportSpec ()
makeImportSpec (NamespacedName namespace q) qs
  | Set.null qs = Hs.IAbs () namespace q
  | otherwise   = Hs.IThingWith () q $ map makeCName $ Set.toList qs

makeImportDecl :: Hs.ModuleName () -> Qualifier -> Maybe ImportSpecMap -> Hs.ImportDecl ()
makeImportDecl mod qual specs = Hs.ImportDecl ()
  mod (isQualified qual) False False Nothing (qualifiedAs qual)
  (Hs.ImportSpecList ()
        False                                             -- whether the list should be a list of hidden identifiers ('hiding')
        . map (uncurry makeImportSpec) . Map.toList <$> specs)

--------------------------------------------------------------------------------
-- compile exports

compileExport :: Export -> Hs.ExportSpec ()
compileExport = \case
  ExportFun name -> Hs.EVar () (Hs.UnQual () name)
  ExportType name | Hs.isOpName name ->
    Hs.EAbs () (Hs.TypeNamespace ()) (Hs.UnQual () name)
  ExportType name -> Hs.EAbs () (Hs.NoNamespace ()) (Hs.UnQual () name)
  ExportData name -> Hs.EThingWith () (Hs.EWildcard () 0) (Hs.UnQual () name) []
  ExportClass name -> Hs.EThingWith () (Hs.EWildcard () 0) (Hs.UnQual () name) []
  ExportModule mname -> Hs.EModuleContents () mname
