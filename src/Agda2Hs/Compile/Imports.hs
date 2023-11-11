module Agda2Hs.Compile.Imports ( compileImports, preludeImportDecl ) where

import Data.Char ( isUpper )
import Data.List ( isPrefixOf )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend
import Agda.TypeChecking.Pretty ( text )
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

type ImportSpecMap = Map NamespacedName (Set NamespacedName)
type ImportDeclMap = Map (Hs.ModuleName (), Qualifier) ImportSpecMap

compileImports :: String -> Imports -> TCM [Hs.ImportDecl ()]
compileImports top is0 = do
  let is = filter (not . (top `isPrefixOf`) . Hs.prettyPrint . importModule) is0
  checkClashingImports is
  let imps = Map.toList $ groupModules is
  return $ map (uncurry $ uncurry makeImportDecl) imps
  where
    mergeChildren :: ImportSpecMap -> ImportSpecMap -> ImportSpecMap
    mergeChildren = Map.unionWith Set.union

    makeSingle :: Maybe NamespacedName -> NamespacedName -> ImportSpecMap
    makeSingle Nothing  q = Map.singleton q Set.empty
    makeSingle (Just p) q = Map.singleton p $ Set.singleton q

    groupModules :: [Import] -> ImportDeclMap
    groupModules = foldr
      (\(Import mod as p q ns) -> Map.insertWith mergeChildren (mod,as)
                                                                (makeSingle (parentNN p) (NamespacedName ns q)))
      Map.empty
        where
          parentNN :: Maybe (Hs.Name ()) -> Maybe NamespacedName
          parentNN (Just name@(Hs.Symbol _ _)) = Just $ NamespacedName (Hs.TypeNamespace ()) name
                                                                        -- ^ for parents, if they are operators, we assume they are type operators
                                                                        -- but actually, this will get lost anyway because of the structure of ImportSpec
                                                                        -- the point is that there should not be two tuples with the same name and diffenrent namespaces
          parentNN (Just name)                 = Just $ NamespacedName (Hs.NoNamespace ())   name
          parentNN Nothing                     = Nothing

    -- TODO: avoid having to do this by having a CName instead of a
    -- Name in the Import datatype
    makeCName :: Hs.Name () -> Hs.CName ()
    makeCName n@(Hs.Ident _ s)
      | isUpper (head s) = Hs.ConName () n
      | otherwise        = Hs.VarName () n
    makeCName n@(Hs.Symbol _ s)
      | head s == ':' = Hs.ConName () n
      | otherwise     = Hs.VarName () n

    makeImportSpec :: NamespacedName -> Set NamespacedName -> Hs.ImportSpec ()
    makeImportSpec (NamespacedName namespace q) qs
      | Set.null qs = Hs.IAbs () namespace q
      | otherwise   = Hs.IThingWith () q $ map (makeCName . nnName) $ Set.toList qs

    makeImportDecl :: Hs.ModuleName () -> Qualifier -> ImportSpecMap -> Hs.ImportDecl ()
    makeImportDecl mod qual specs = Hs.ImportDecl ()
      mod (isQualified qual) False False Nothing (qualifiedAs qual)
      (Just $ Hs.ImportSpecList ()
            False                                             -- whether the list should be a list of hidden identifiers ('hiding')
            $ map (uncurry makeImportSpec) $ Map.toList specs)

    checkClashingImports :: Imports -> TCM ()
    checkClashingImports [] = return ()
    checkClashingImports (Import mod as p q _ : is) =
      case filter isClashing is of
        (i : _) -> genericDocError =<< text (mkErrorMsg i)
        []      -> checkClashingImports is
     where
        isClashing (Import _ as' p' q' _) = (as' == as) && (p' /= p) && (q' == q)
        mkErrorMsg (Import _ _ p' q' _) =
             "Clashing import: " ++ pp q ++ " (both from "
          ++ prettyShow (pp <$> p) ++ " and "
          ++ prettyShow (pp <$> p') ++ ")"
        -- TODO: no range information as we only have Haskell names at this point


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
