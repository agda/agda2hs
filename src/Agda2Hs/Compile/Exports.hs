module Agda2Hs.Compile.Exports ( compileExports ) where

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
import Agda.TypeChecking.Pretty ( text, vsep, prettyList_, (<+>) )
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Utils.Monad ( when )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils

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
