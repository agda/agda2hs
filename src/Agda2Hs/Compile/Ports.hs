-- Compiling (im|ex)ports
module Agda2Hs.Compile.Ports ( compilePorts, hasHaskellExports, tellDefinitionExport ) where

import Control.Monad.Reader ( asks )

import Data.Char ( isUpper )
import qualified Data.List as L
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Containers.ListUtils ( nubOrd )

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( validVarId, validConId, validModuleName, pp )

import Agda.Compiler.Backend
import Agda.TypeChecking.Pretty ( pretty, text, prettyList_, (<+>) )
import Agda.Syntax.Position ( Range, getRange, HasRange )
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Info
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Scope.Base
import Agda.Syntax.Common
import Agda.Syntax.Internal ( unDom, conName )
import Agda.Syntax.Common.Pretty ( prettyShow, Pretty, Doc )
import Agda.Utils.Maybe ( fromMaybe, isJust )
import Agda.Utils.Monad ( liftM2, andM, anyM, ifM, ifNotM, forM_, when, whenM, unless, filterM )
import Agda.Utils.Impossible
import qualified Agda.Utils.Null as Null

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Pragma ( processPragma )

--------------------------------------------------------------------------------
-- main

-- | Compile the imports and exports of a module,
--   with special handling for the @Prelude@ as prescribed by the 'PreludeOptions'.
compilePorts
  :: PreludeOptions -> String -> ModuleEnv -> Imports -> Exports
  -> TCM ([Hs.ImportDecl ()], Hs.ExportSpecList ())
compilePorts preOpts@PreludeOpts{..} top menv imps0 es0 = do
  topInfo <- moduleAbstrSyn menv
  reexps <- collectReexports topInfo
  reexps <- foldMap (translateReexport (moduleName menv)) reexps

  let isPrelude = (== Hs.prelude_mod ())

  -- the 'hiding' list also applies to the reexport of the prelude, which would
  -- silently not export the hidden names
  when (preludeImplicit && not (null preludeHiding)) $
    forM_ reexps $ \(ReexportModule m _ r) ->
      when (isPrelude m) $
        badReexport r (pp m) "not supported when the prelude config has 'hiding'"

  let -- if Prelude is imported implicitly, we remove all prelude imports, including those of reexports
      is0 = map toImport reexps ++ imps0
      is1 | preludeImplicit = filter (not . isPrelude . importModule) is0
          | otherwise       = is0

      -- and add back the configured one:
      preludeImport = [preludeImportDecl preOpts | preludeImplicit]

      toExport' r@(ReexportModule m _ _)
        -- export Prelude directly because we throwed away explicit imports of Prelude
        | preludeImplicit && isPrelude m = ExportModule m
        | otherwise = toExport r

  let is = filter ((top /=) . Hs.prettyPrint . importModule) is1
  checkClashingImports is
  let imps = Map.toList $ groupImports is
  reportSLn "agda2hs.import" 10 $ "All imported modules: " ++ show (map (pp . fst . fst) imps)
  let impDecls = preludeImport ++ map (uncurry $ uncurry makeImportDecl) imps

  let exps = map compileExport $ nubOrd $ map toExport' reexps ++ es0
  -- TODO(satoshi): check clashing exports
  reportSDoc "agda2hs.export" 10 $
    "All exports:" <+> prettyList_ (map (text . pp) exps)

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

-- | Does the Haskell module corresponding to the given Agda module export anything?
-- NOTE: This function may over-approximate, inheriting hasHaskellEntity
hasHaskellExports :: TopLevelModuleName -> TCM Bool
hasHaskellExports mname = do
  iface <- maybe __IMPOSSIBLE__ miInterface <$> getVisitedModule mname
  let pubNames = publicNames $ iInsideScope iface
  reportSDoc "agda2hs.export" 30 $ do
    hsNames <- filterSetA (hasHaskellEntity . anameName) pubNames
    pretty mname <+> "exports:" <+> pretty hsNames
  anyM (hasHaskellEntity . anameName) pubNames
  where
    -- TODO(satoshi): use Set.filterA when we start using containers>=0.8.1
    filterSetA :: (Applicative m) => (a -> m Bool) -> Set a -> m (Set a)
    filterSetA p = fmap Set.fromDistinctAscList . filterM p . Set.toAscList

data Reexport
  = ReexportModule (Hs.ModuleName ()) (Maybe (Hs.ModuleName ())) Range

type Reexports = [Reexport]

toImport :: Reexport -> Import
toImport = \case
  ReexportModule m as _ -> ImportModule m as

toExport :: Reexport -> Export
toExport = \case
  ReexportModule m as _ -> ExportModule (fromMaybe m as)

data AgdaReexport = AgdaReexport
  { agdaReexpRange  :: Range
  , agdaReexpModule :: TopLevelModuleName
  , agdaReexpAs     :: Maybe C.Name
  }

collectReexports :: TopLevelInfo -> TCM [AgdaReexport]
collectReexports topInfo = go False $ insideDecls topInfo
  where
    go nested = foldMap $ \case
      A.Section _ _ m _ decls | isPubMod m -> go True decls

      A.Import minfo m dir@(isOpenPublic -> True)
        | nested ->
            badReexport minfo m "reexports inside nested modules are not supported"
        | not (null (impRenaming dir)) ->
            badReexport minfo m "'renaming' directive is not supported"
        | not (Null.null dir) -> do
            -- TODO(satoshi): support 'using' and 'hiding'
            [] <$ warnDropReexport minfo m "'using' and 'hiding' are not supported yet"
        | otherwise -> do
            tlm <- getTopLevelModuleForModuleName m
            pure [AgdaReexport (getRange minfo) tlm (minfoAsName minfo)]

      -- 'import M' followed by a separate 'open M public'
      A.Open minfo m dir@(isOpenPublic -> True)
        | not (isInCurrMod m) ->
            badReexport minfo m "reexporting with a separate 'open ... public' is not supported"

      -- module applications, e.g. 'open import M args public'
      A.Apply minfo _ _ (A.SectionApp _ m _) _ dir
        | isOpenPublic dir || any isOpenPublic (minfoDirective minfo), not (isInCurrMod m) ->
            badReexport minfo m "reexporting module applications is not supported"

      _ -> pure []

    isInCurrMod =
      let curr = _scopeCurrent $ topLevelScope topInfo
       in (`A.isLeChildModuleOf` curr)

    isPubMod =
      let pubMods = publicModules $ topLevelScope topInfo
       in \m -> A.isAnonymousModuleName m || Map.member m pubMods

    isOpenPublic = isJust . publicOpen


translateReexport :: TopLevelModuleName -> AgdaReexport -> TCM Reexports
translateReexport current (AgdaReexport range tlm asName) =
  case hsModuleKind tlm of
    PrimModule
      -- TODO(satoshi): once PrimModules only contain items with a Prelude
      -- counterpart, compile this to an explicit list of those items.
      | prettyShow tlm /= "Haskell.Prelude" ->
          [] <$ warnDropReexport range tlm "not supported yet"
      | otherwise -> translate
    _ -> ifNotM (hasHaskellExports tlm) (pure []) translate
  where
    translate = do
      (kind, mod) <- compileTopLevelModuleName tlm
      checkNameClash kind mod
      asName <- traverse compileModuleAlias asName
      pure [ReexportModule mod asName range]

    -- Dropping the 'Haskell' prefix of a reexported Haskell module may result
    -- in a name clash, e.g. reexporting 'Haskell.Data.Map' from 'Data.Map'.
    checkNameClash kind mod' =
      when (kind == HsModule && pp mod' == prettyShow current) $
        badReexport range tlm "name clash after dropping the 'Haskell.' prefix"

    compileModuleAlias name = do
      let name' = Hs.hsModuleName $ prettyShow name
      unless (validModuleName name') $
        badReexport range tlm $ pretty name <+> "is not a valid Haskell module name"
      pure name'


badReexport :: (HasRange r, Pretty mod) => r -> mod -> TCM Doc -> TCM a
badReexport range mod reason = setCurrentRange range $ agda2hsErrorM $
  "Cannot compile reexport of" <+> (pretty mod <> ":") <+> reason

warnDropReexport :: (HasRange r, Pretty mod) => r -> mod -> TCM Doc -> TCM ()
warnDropReexport range mod reason = setCurrentRange range $ agda2hsWarningM $
  "Dropping reexport of" <+> (pretty mod <> ":") <+> reason

--------------------------------------------------------------------------------
-- compile imports

type ImportSpecMap = Map NamespacedName (Set (Hs.Name ()))
type ImportDeclMap = Map (Hs.ModuleName (), Qualifier) (Maybe ImportSpecMap)

checkClashingImports :: Imports -> TCM ()
checkClashingImports [] = return ()
checkClashingImports (Import mod as p (NamespacedName _ q) r : is) =
  case filter isClashing is of
    (i : _) -> setCurrentRange r $ agda2hsStringError $ mkErrorMsg i
    []      -> checkClashingImports is
  where
    isClashing (Import _ as' p' (NamespacedName _ q') _) =
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
    mkErrorMsg (Import _ _ p' (NamespacedName _ q') _) =
          "Clashing import: " ++ pp q ++ " (both from "
      ++ prettyShow (pp . nnName <$> p) ++ " and "
      ++ prettyShow (pp . nnName <$> p') ++ ")"
checkClashingImports (ImportInstances mod : is) = checkClashingImports is
checkClashingImports (ImportModule mod _ : is) = checkClashingImports is

groupImports :: Imports -> ImportDeclMap
groupImports = flip foldr Map.empty $ \case
  (Import mod as parent name _) ->
    Map.insertWith mergeChildren (mod,as) (makeSingle parent name)
  (ImportInstances mod) ->
    Map.insertWith mergeChildren (mod, Unqualified Nothing) (Just mempty)
  (ImportModule mod as) ->
    Map.insertWith mergeChildren (mod, Unqualified as) Nothing
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
  mod (isQualified qual) False False Nothing (importAlias qual)
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
  ExportDataCons name cons ->
    Hs.EThingWith () (Hs.NoWildcard ()) (Hs.UnQual () name) (map (Hs.ConName ()) cons)
  ExportClass name -> Hs.EThingWith () (Hs.EWildcard () 0) (Hs.UnQual () name) []
  ExportModule mname -> Hs.EModuleContents () mname

-- | Register the export list entries for a definition that is being compiled,
-- unless it should not be exported.
tellDefinitionExport :: Definition -> C ()
tellDefinitionExport def =
  whenM (andM [shouldBeExported (defName def), asks (not . compilingLocal), asks writeExports]) $
    mapM_ tellExport =<< definitionExport def

-- | The export list entries corresponding to a definition, if any.
--
-- This is the single source of truth for how definitions are exported: it is
-- used both for definitions compiled by agda2hs and for definitions that are
-- bound to an existing Haskell definition (marked with the @existing@ or
-- @existing-class@ keyword).
definitionExport :: Definition -> C [Export]
definitionExport def = case theDef def of
  Function{} -> do
    e <- ifM (endsInSort $ defType def)
           (ExportType <$> functionName)
           (ExportFun <$> functionName)
    pure [e]
  Axiom{}    -> pure [ExportFun typeName]
  Datatype{} -> pure [ExportData typeName]
  Record{}   -> do
    p <- processPragma (defName def)
    if isClassPragma p then pure [ExportClass typeName] else recordExport def
  _          -> pure []
  where
    typeName     = compileName (qnameName $ defName def)
    functionName = Hs.unQual <$> compileQName (defName def)

-- | The export entries for a record compiled as a Haskell data type. The
-- constructor is always exported, but a field is only exported if its
-- projection is exported from the module that defines the record, i.e. if the
-- record module is opened publicly there.
recordExport :: Definition -> C [Export]
recordExport def = do
  let tn = compileName (qnameName $ defName def)
      Record{ recFields, recConHead, recNamedCon } = theDef def
      cn = if recNamedCon then compileName (qnameName $ conName recConHead) else tn
  publicFields <- filterM (isExportedProjection . unDom) recFields
  if length publicFields == length recFields then pure [ExportData tn] else
    pure $ ExportDataCons tn [cn] : map (ExportFun . compileName . qnameName . unDom) publicFields
