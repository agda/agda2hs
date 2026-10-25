module Agda2Hs.Compile.Exports ( tellDefinitionExport ) where

import Control.Monad.Reader ( asks )

import Agda.Compiler.Backend
import Agda.Utils.Maybe ( whenJustM )
import Agda.Utils.Monad ( andM, whenM, ifM )

import Agda2Hs.AgdaUtils ( endsInSort )
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils ( tellExport, shouldBeExported, isClassPragma, compileName )
import Agda2Hs.Pragma

import qualified Agda2Hs.Language.Haskell as Hs

-- | Register the export list entry for a definition that is being compiled,
-- unless it should not be exported.
tellDefinitionExport :: Definition -> C ()
tellDefinitionExport def =
  whenM (andM [shouldBeExported (defName def), asks (not . compilingLocal), asks writeExports]) $
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
