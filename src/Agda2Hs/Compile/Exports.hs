module Agda2Hs.Compile.Exports ( compileExports, tellDefinitionExport ) where

import Control.Monad ( filterM )
import Control.Monad.Reader ( asks )

import Agda.Compiler.Backend
import Agda.Syntax.Internal ( unDom, conName )
import Agda.TypeChecking.Pretty ( text, prettyList_, (<+>) )
import Agda.Utils.Monad ( and2M, whenM, ifM )

import Agda2Hs.AgdaUtils ( endsInSort )
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
  ( tellExport, shouldBeExported, isClassPragma, isExportedProjection, compileName )
import Agda2Hs.Pragma

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( pp )

compileExports :: Exports -> TCM (Hs.ExportSpecList ())
compileExports exps = do
  let exps' = map compileExport exps
  reportSDoc "agda2hs.export" 10 $
    "All exports: " <+> prettyList_ (map (text . pp) exps')
  pure $ Hs.ExportSpecList () exps'

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

-- | Register the export list entries for a definition that is being compiled,
-- unless it should not be exported.
tellDefinitionExport :: Definition -> C ()
tellDefinitionExport def =
  whenM (shouldBeExported (defName def) `and2M` asks writeExports) $
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
