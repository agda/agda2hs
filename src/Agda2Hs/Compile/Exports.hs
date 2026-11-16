module Agda2Hs.Compile.Exports ( compileExports, tellDefinitionExport ) where

import Control.Monad.Reader ( asks )

import Agda.Compiler.Backend
import Agda.TypeChecking.Pretty ( text, prettyList_, (<+>) )
import Agda.Utils.Maybe ( whenJustM )
import Agda.Utils.Monad ( and2M, whenM, ifM )

import Agda2Hs.AgdaUtils ( endsInSort )
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils ( tellExport, shouldBeExported, isClassPragma, compileName )
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
  ExportClass name -> Hs.EThingWith () (Hs.EWildcard () 0) (Hs.UnQual () name) []

-- | Register the export list entry for a definition that is being compiled,
-- unless it should not be exported.
tellDefinitionExport :: Definition -> C ()
tellDefinitionExport def =
  whenM (shouldBeExported (defName def) `and2M` asks writeExports) $
    whenJustM (definitionExport def) tellExport

-- | The export list entry corresponding to a definition, if any.
--
-- This is the single source of truth for how definitions are exported: it is
-- used both for definitions compiled by agda2hs and for definitions that are
-- bound to an existing Haskell definition (marked with the @existing@ or
-- @existing-class@ keyword).
definitionExport :: Definition -> C (Maybe Export)
definitionExport def = case theDef def of
  Function{} -> Just <$> ifM (endsInSort $ defType def)
    (ExportType <$> functionName)
    (ExportFun <$> functionName)
  Axiom{}    -> Just . ExportFun <$> typeName
  Datatype{} -> Just . ExportData <$> typeName
  Record{}   -> do
    p <- processPragma (defName def)
    Just <$> if isClassPragma p
      then ExportClass <$> typeName
      else ExportData <$> typeName
  _          -> pure Nothing
  where
    typeName     = pure $ compileName (qnameName $ defName def)
    functionName = Hs.unQual <$> compileQName (defName def)
