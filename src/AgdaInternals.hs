{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- TODO: merge upstream, useful for other backends
{-# LANGUAGE TypeFamilies #-}

module AgdaInternals where

import Control.Monad.State
import Control.Monad.Writer

import Data.String

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.Utils.Size

instance Subst Clause where
  type SubstArg Clause = DeBruijnPattern
  applySubst rhoP c@Clause {..} =
    c
      { clauseTel = applyPatSubst rhoP clauseTel
      , namedClausePats = applySubst rhoP' namedClausePats
      , clauseBody = applyPatSubst rhoP' clauseBody
      , clauseType = applyPatSubst rhoP' clauseType
      }
    where
      rhoP' = liftS (size clauseTel) rhoP

instance Subst Defn where
  type SubstArg Defn = DeBruijnPattern
  applySubst rhoP = \case
    f@Function {..} ->
      f
        { funClauses = applySubst rhoP <$> funClauses
        , funCovering = applySubst rhoP <$> funCovering
        }
    (PrimitiveSort q s) -> PrimitiveSort q (applyPatSubst rhoP s)
    d -> d

instance Subst Definition where
  type SubstArg Definition = DeBruijnPattern
  applySubst rhoP d@Defn {..} =
    d {defType = applyPatSubst rhoP defType, theDef = applySubst rhoP theDef}

instance (Monoid r, MonadFresh i m) => MonadFresh i (WriterT r m)
instance (Monoid r, MonadInteractionPoints m) => MonadInteractionPoints (WriterT r m)
instance (Monoid r, MonadStConcreteNames m) => MonadStConcreteNames (WriterT r m) where
  -- runStConcreteNames :: StateT ConcreteNames (WriterT r m) a -> WriterT r m a
  runStConcreteNames m = WriterT $ runStConcreteNames $ StateT $ \s -> do
    ((x, s'), ns) <- runWriterT $ runStateT m s
    return ((x, ns), s')
instance (Monoid r, Monad m, IsString (m a)) => IsString (WriterT r m a) where
  fromString s = WriterT $ ((,mempty) <$> fromString s)
instance (Monoid r, MonadBlock m) => MonadBlock (WriterT r m) where
  catchPatternErr h m = WriterT $ catchPatternErr (runWriterT . h) (runWriterT m)
instance (MonadBlock m) => MonadBlock (StateT s m) where
  catchPatternErr h m = StateT $ \s -> catchPatternErr (flip runStateT s . h) (runStateT m s)
