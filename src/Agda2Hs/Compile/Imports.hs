
module Agda2Hs.Compile.Imports where

import Data.List ( isPrefixOf )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

compileImports :: String -> [(Hs.ModuleName (), Hs.QName ())] -> TCM [Hs.ImportDecl ()]
compileImports top qs = do
  let qs' = filter (not . (top `isPrefixOf`) . Hs.prettyPrint . fst) qs
  let imps = Map.toList $ groupModules qs'
  traverse (uncurry makeImport) imps

  where
    groupModules :: [(Hs.ModuleName (), Hs.QName ())] -> Map (Hs.ModuleName ()) (Set (Hs.QName ()))
    groupModules = foldr (\(mod, q) -> Map.insertWith Set.union mod (Set.singleton q)) Map.empty

    makeImport :: Hs.ModuleName () -> Set (Hs.QName ()) -> TCM (Hs.ImportDecl ())
    makeImport mod names = do
      return $ Hs.ImportDecl ()
        mod False False False Nothing Nothing
        (Just $ Hs.ImportSpecList () False (map (Hs.IVar ()) $ map unQual $ Set.toList names))
