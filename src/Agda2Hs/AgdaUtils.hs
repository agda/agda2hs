module Agda2Hs.AgdaUtils where

import Data.Data
import Data.Monoid ( Any(..) )
import qualified Data.Map as Map
import Data.Maybe ( fromMaybe )

import Agda.Compiler.Backend hiding ( Args )

import Agda.Interaction.FindFile ( findFile' )

import Agda.Syntax.Common ( Arg, defaultArg )
import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.TopLevelModuleName

import Agda.TypeChecking.Monad ( topLevelModuleName )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce ( reduceDefCopy )

import Agda.Utils.Either ( isRight )
import Agda.Utils.List ( initMaybe )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Monad ( ifM )
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

-- | Check whether the given name (1) is the name of an extended
--   lambda and (2) is used anywhere inside the second argument.
extLamUsedIn :: NamesIn a => QName -> a -> Bool
extLamUsedIn n x = isExtendedLambdaName n && getAny (namesIn' (Any . (n ==)) x)

-- | All mentions of local definitions that occur anywhere inside the argument.
getLocalUses :: NamesIn a => [QName] -> a -> [QName]
getLocalUses ls = namesIn' $ \q -> [ q | q `elem` ls ]

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

-- | Map over the body of all clauses of a function definition.
mapDef :: (Term -> Term) -> Definition -> Definition
mapDef f d = d{ theDef = mapDefn (theDef d) }
  where
    mapDefn def@Function{} = def{ funClauses = map mapClause (funClauses def) }
    mapDefn defn = defn

    mapClause c = c{ clauseBody = f <$> clauseBody c }

topLevelModuleNameForModuleName :: ModuleName -> TCM TopLevelModuleName
topLevelModuleNameForModuleName = topLevelModuleName . rawTopLevelModuleNameForModuleName

isTopLevelModule :: ModuleName -> TCM (Maybe TopLevelModuleName)
isTopLevelModule m = do
  tlm <- topLevelModuleNameForModuleName m
  ifM (isRight <$> findFile' tlm) (return $ Just tlm) (return Nothing)

-- | Get the toplevel module parent to a given module.
getTopLevelModuleForModuleName :: ModuleName -> TCM TopLevelModuleName
getTopLevelModuleForModuleName = loop . mnameToList
  where
    loop ns
      | null ns   = __IMPOSSIBLE__
      | otherwise = isTopLevelModule (MName ns) >>= \case
          Nothing  -> loop (init ns)
          Just tlm -> return tlm

-- | Get the toplevel module parent to a given a name.
getTopLevelModuleForQName :: QName -> TCM TopLevelModuleName
getTopLevelModuleForQName = getTopLevelModuleForModuleName . qnameModule

lookupModuleInCurrentModule :: C.Name -> TCM [AbstractModule]
lookupModuleInCurrentModule x =
  List1.toList' . Map.lookup x . nsModules . thingsInScope [PublicNS, PrivateNS] <$> getCurrentScope

-- | Try to unfold a definition if introduced by module application.
maybeUnfoldCopy
  :: PureTCM m
  => QName -- ^ Name of the definition.
  -> Elims
  -> (Term -> m a)
  -- ^ Callback if the definition is indeed a copy.
  -> (QName -> Elims -> m a)
  -- ^ Callback if the definition isn't a copy.
  -> m a
maybeUnfoldCopy f es onTerm onDef =
  reduceDefCopy f es >>= \case
    NoReduction ()   -> onDef f es
    YesReduction _ t -> onTerm t
