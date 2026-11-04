module Agda2Hs.Compile.Exports ( compileExports ) where

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( pp )
import Agda.Compiler.Backend
import Agda.TypeChecking.Pretty ( text, prettyList_, (<+>) )
import Agda2Hs.Compile.Types

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
