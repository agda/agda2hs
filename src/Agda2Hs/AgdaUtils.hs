module Agda2Hs.AgdaUtils where

import Data.Data
import Data.Generics ( listify )
import Data.Maybe ( fromMaybe )

import Agda.Compiler.Backend hiding ( Args )

import Agda.Syntax.Common ( Arg, defaultArg )
import Agda.Syntax.Internal

import Agda.TypeChecking.Pretty ( Doc, text, vcat )
import Agda.TypeChecking.Substitute

import Agda.Utils.List
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import AgdaInternals

multilineText :: Monad m => String -> m Doc
multilineText s = vcat $ map text $ lines s

(~~) :: QName -> String -> Bool
q ~~ s = prettyShow q == s

-- | Check whether a module is an *immediate* parent of another.
isFatherModuleOf :: ModuleName -> ModuleName -> Bool
isFatherModuleOf m = maybe False (mnameToList m ==) . initMaybe . mnameToList

-- | Apply a clause's telescope arguments to a local where definition.
-- i.e. reverse Agda's λ-lifting
applyUnderTele :: Definition -> Args -> Definition
applyUnderTele d as = raise (length as) d `apply` as

-- | Check whether an extended lambda is used anywhere inside given argument.
extLamUsedIn :: Data a => QName -> a -> Bool
extLamUsedIn n = (n `elem`) . listify isExtendedLambdaName

-- | All mentions of local definitions that occur anywhere inside the argument.
getLocalUses :: Data a => [(QName, Definition)] -> a -> [QName]
getLocalUses ls = listify (`elem` map fst ls)

-- | Convert the final 'Proj' projection elimination into a
--   'Def' projection application.
unSpine1 :: Term -> Term
unSpine1 v =
  case hasElims v of
    Just (h, es) -> fromMaybe v $ loop h [] es
    Nothing      -> v
  where
    loop :: (Elims -> Term) -> Elims -> Elims -> Maybe Term
    loop h res es =
      case es of
        []             -> Nothing
        Proj o f : es' -> Just $ fromMaybe (Def f (Apply (defaultArg v) : es')) $ loop h (Proj o f : res) es'
        e        : es' -> loop h (e : res) es'
      where v = h $ reverse res

mapDef :: (Term -> Term) -> Definition -> Definition
mapDef f d = d{ theDef = mapDefn (theDef d) }
  where
    mapDefn def@Function{} = def{ funClauses = map mapClause (funClauses def) }
    mapDefn defn = defn -- We only need this for Functions

    mapClause c = c{ clauseBody = f <$> clauseBody c }
