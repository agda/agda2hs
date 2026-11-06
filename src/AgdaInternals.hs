-- TODO: merge upstream, useful for other backends
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module AgdaInternals where

import Control.Monad.Writer
import Control.Monad.State

import Data.Maybe ( mapMaybe )

import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding ( pretty )
import Agda.TypeChecking.Substitute
import Agda.Utils.Size
import qualified Agda.Utils.Set1 as Set1

instance Subst Clause where
  type SubstArg Clause = DeBruijnPattern
  applySubst rhoP c@Clause{..} = c
      { clauseTel       = applyPatSubst rhoP clauseTel
      , namedClausePats = applySubst rhoP' namedClausePats
      , clauseBody      = applyPatSubst rhoP' clauseBody
      , clauseType      = applyPatSubst rhoP' clauseType
      } where rhoP' = liftS (size clauseTel) rhoP

instance Subst Defn where
  type SubstArg Defn = DeBruijnPattern
  applySubst rhoP = \case
    f@Function{..} ->
       f { funClauses  = applySubst rhoP <$> funClauses
         , funCovering = applySubst rhoP <$> funCovering }
    (PrimitiveSort q s) -> PrimitiveSort q (applyPatSubst rhoP s)
    d -> d

instance Subst Definition where
  type SubstArg Definition = DeBruijnPattern
  applySubst rhoP d@Defn{..} =
    d {defType = applyPatSubst rhoP defType, theDef = applySubst rhoP theDef}

instance (Monoid r, MonadBlock m) => MonadBlock (WriterT r m) where
  catchPatternErr h m = WriterT $ catchPatternErr (runWriterT . h) (runWriterT m)
instance MonadBlock m => MonadBlock (StateT s m) where
  catchPatternErr h m = StateT $ \s -> catchPatternErr (flip runStateT s . h) (runStateT m s)

-- ** Provenance of local where-definitions.

-- | The where-modules attached to a function's clauses.
defWhereModules :: Definition -> [ModuleName]
defWhereModules = mapMaybe clauseWhereModule . defClauses

-- | Check whether a name is declared inside a where-block of a given function.
inWhereBlockOf :: QName -> Definition -> Bool
inWhereBlockOf q = any (qnameModule q `isLeChildModuleOf`) . defWhereModules

-- ** Pretty

instance Pretty a => Pretty (Set1.Set1 a) where
  pretty xs = pretty (Set1.toSet xs)

instance PrettyTCM a => PrettyTCM (Set1.Set1 a) where
  prettyTCM xs = prettyTCM (Set1.toSet xs)
