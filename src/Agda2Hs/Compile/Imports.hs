
module Agda2Hs.Compile.Imports ( compileImports ) where

import Data.Char ( isUpper )
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

type ImportSpecMap = Map (Hs.Name ()) (Set (Hs.Name ()))
type ImportDeclMap = Map (Hs.ModuleName (), Qualifier) ImportSpecMap

compileImports :: String -> Imports -> TCM [Hs.ImportDecl ()]
compileImports top is0 = do
  let is = filter (not . (top `isPrefixOf`) . Hs.prettyPrint . importModule) is0
  let imps = Map.toList $ groupModules is
  return $ map (uncurry $ uncurry makeImportDecl) imps

  where
    mergeChildren :: ImportSpecMap -> ImportSpecMap -> ImportSpecMap
    mergeChildren = Map.unionWith Set.union

    makeSingle :: Maybe (Hs.Name ()) -> Hs.Name () -> ImportSpecMap
    makeSingle Nothing  q = Map.singleton q Set.empty
    makeSingle (Just p) q = Map.singleton p $ Set.singleton q

    groupModules :: [Import] -> ImportDeclMap
    groupModules = foldr
      (\(Import mod as p q) -> Map.insertWith mergeChildren (mod,as) (makeSingle p q)) Map.empty

    -- TODO: avoid having to do this by having a CName instead of a
    -- Name in the Import datatype
    makeCName :: Hs.Name () -> Hs.CName ()
    makeCName n@(Hs.Ident _ s)
      | isUpper (head s) = Hs.ConName () n
      | otherwise        = Hs.VarName () n
    makeCName n@(Hs.Symbol _ s)
      | head s == ':' = Hs.ConName () n
      | otherwise     = Hs.VarName () n

    makeImportSpec :: Hs.Name () -> Set (Hs.Name ()) -> Hs.ImportSpec ()
    makeImportSpec q qs
      | Set.null qs = Hs.IVar () q
      | otherwise   = Hs.IThingWith () q $ map makeCName $ Set.toList qs

    makeImportDecl :: Hs.ModuleName () -> Qualifier -> ImportSpecMap -> Hs.ImportDecl ()
    makeImportDecl mod qual specs = Hs.ImportDecl ()
      mod (isQualified qual) False False Nothing (qualifiedAs qual)
      (Just $ Hs.ImportSpecList () False $ map (uncurry makeImportSpec) $ Map.toList specs)

    isQualified :: Qualifier -> Bool
    isQualified = \case
      Unqualified     -> False
      (QualifiedAs _) -> True

    qualifiedAs :: Qualifier -> Maybe (Hs.ModuleName ())
    qualifiedAs = \case
      Unqualified     -> Nothing
      (QualifiedAs m) -> m
