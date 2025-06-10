-- TODO: merge upstream, useful for other backends
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module AgdaInternals where

import Control.Monad.Writer
import Control.Monad.State

import Data.String

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.Utils.Size

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
