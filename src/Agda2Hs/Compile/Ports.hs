-- Compiling (im|ex)ports
module Agda2Hs.Compile.Ports ( compilePorts, preludeImportDecl ) where

import Data.Bifunctor ( bimap, first )
import Data.Char ( isUpper )
import Data.List ( isPrefixOf )
import qualified Data.List as L
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( validVarId, validConId, pp )

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.TypeChecking.Pretty ( pretty, text, vsep, prettyList_, (<+>), vcat )
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Scope.Base
import Agda.Syntax.Info as A
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Utils.Monad ( when, liftM2, forMaybeM, concatMapM )
import Agda.Utils.Impossible

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

data Reexport
  = ReexportModule (Hs.ModuleName ())

type Reexports = [Reexport]

toImport :: Reexport -> Import
toImport = \case
  ReexportModule m -> ImportModule m

toExport :: Reexport -> Export
toExport = \case
  ReexportModule m -> ExportModule m

pattern OpenImportDirective { using, hiding, impRenaming }
  <- ImportDirective { publicOpen = Just _, using, hiding, impRenaming}

extractReexports :: ModuleEnv -> TCM Reexports
extractReexports menv = do
  allImports <- getImports . topLevelDecls <$> moduleAbstrSyn menv
  flip concatMapM allImports $ \(mod, directive) -> case directive of
    OpenImportDirective { using = UseEverything , hiding = [] , impRenaming = [] } -> do
      (kind, m) <- compileModuleName' mod
      case kind of
        PrimModule -> error "TODO"
        HsModule -> error "TODO"
        AgdaModule -> pure [ReexportModule m]
    _ -> pure []
  where
    -- FIXME(wasabi315): track imports in nested modules
    -- an open-public-ed nested module may reexports other modules
    getImports = \case
      [A.Section _ _ _ _ decls] ->
        let go = \case
              A.Import _ modName impDir -> pure (modName, impDir)
              A.ScopedDecl _ decls -> go =<< decls
              _ -> []
         in go =<< decls
      -- discard imports before module header because they can't be open-public-ed.
      (_ : decls) -> getImports decls
      _ -> __IMPOSSIBLE__

{-

- Don't reexport modules that does not contain any AGDA2HS COMPILE (default|class|newtype|existing-class|compile-to) pragma
- Unless the module name is prefixed by Haskell.
  - drop Haskell. prefix

- Regarding compile-to
  - suppose module M1 defines a datatype T1, module M2 defines T2 with COMPILE T2 to T1
  - what do we wanna do if module M3 reexports M2?
  - we don't wanna do
      * generate empty module for M2
      * generate reexport of that empty module in Haskell module for M3!

- removing transparent/inline definitions from export list
  - we keep the set of such names in GlobalEnv

- what about special names?

- compileQName is in C monad!
  - needs access to various envs to determine the kind of names
    - we could manually thread the envs, but this needs a big refactoring because util funs are built around C
  - compileQName is overloaded right now
    - calls tellImport and tellTypeOperator inside, beyond just compiling names

-}

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
    isClashing (Import _ as' p' (NamespacedName _ q')) = (as' == as) && (p' /= p) && (q' == q)
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
