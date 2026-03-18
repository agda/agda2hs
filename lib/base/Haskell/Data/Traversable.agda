module Haskell.Data.Traversable where

open import Haskell.Prim hiding (s)
open import Haskell.Prim.Functor
open import Haskell.Prim.Applicative
open import Haskell.Prim.Monad
open import Haskell.Prim.Tuple

open import Haskell.Prim.Traversable public


variable s : Type

for : ⦃ Traversable t ⦄ → ⦃ Applicative f ⦄ → t a → (a → f b) → f (t b)
for = flip traverse

forM :  ⦃ Traversable t ⦄ → ⦃ Monad m ⦄ → t a → (a → m b) → m (t b)
forM = flip mapM

private
  record State (s a : Type) : Type where
    constructor mkState
    pattern
    field run : s → s × a

  record StateT (s : Type) (m : Type → Type) (a : Type) : Type where
    constructor mkStateT
    pattern
    field run : s → m (s × a)

  instance
    open DefaultFunctor
    open ApplicativeFrom<*>

    iDefaultFunctorState : DefaultFunctor (State s)
    iDefaultFunctorState .fmap f (mkState k) = mkState $ λ s → let s' , v = k s in s' , f v

    iFunctorState : Functor (State s)
    iFunctorState = record { DefaultFunctor iDefaultFunctorState }

    iDefaultApplicativeStateL : ApplicativeFrom<*> (State s)
    iDefaultApplicativeStateL .pure x = mkState (λ s → s , x)
    iDefaultApplicativeStateL ._<*>_ (mkState kf) (mkState kx) = mkState $ λ s →
      let s' , f = kf s
          s'' , x = kx s'
      in s'' , f x

    iApplicativeStateL : Applicative (State s)
    iApplicativeStateL = record { ApplicativeFrom<*> iDefaultApplicativeStateL }

    iDefaultApplicativeStateR : ApplicativeFrom<*> (State s)
    iDefaultApplicativeStateR .pure x = mkState (λ s → s , x)
    iDefaultApplicativeStateR ._<*>_ (mkState kf) (mkState kx) = mkState $ λ s →
      let s' , x = kx s
          s'' , f = kf s'
      in s'' , f x

    iApplicativeStateR : Applicative (State s)
    iApplicativeStateR = record { ApplicativeFrom<*> iDefaultApplicativeStateR }

    iDefaultFunctorStateT : ⦃ Monad m ⦄ → DefaultFunctor (StateT s m)
    iDefaultFunctorStateT .fmap f (mkStateT kx) = mkStateT $ λ s → do
      s' , x ← kx s
      return (s' , f x)

    iFunctorStateT : ⦃ Monad m ⦄ → Functor (StateT s m)
    iFunctorStateT = record { DefaultFunctor iDefaultFunctorStateT }

    iDefaultApplicativeStateT : ⦃ Monad m ⦄ → ApplicativeFrom<*> (StateT s m)
    iDefaultApplicativeStateT .pure x = mkStateT (λ s → return (s , x))
    iDefaultApplicativeStateT ._<*>_ (mkStateT kf) (mkStateT kx) = mkStateT $ λ s → do
      s' , f ← kf s
      s'' , x ← kx s'
      return (s'' , f x)

    iApplicativeStateT : ⦃ Monad m ⦄ → Applicative (StateT s m)
    iApplicativeStateT = record { ApplicativeFrom<*> iDefaultApplicativeStateT}

    iDefaultMonadStateT : ⦃ Monad m ⦄ → DefaultMonad (StateT s m)
    iDefaultMonadStateT .DefaultMonad._>>=_ m k = mkStateT $ λ s → do
      s' , x ← StateT.run m s
      StateT.run (k x) s'

    iMonadStateT : ⦃ Monad m ⦄ → Monad (StateT s m)
    iMonadStateT = record { DefaultMonad iDefaultMonadStateT }

mapAccumL : ⦃ Traversable t ⦄ → (s → a → s × b) → s → t a → s × t b
mapAccumL ⦃ iTraversable ⦄ f s t = State.run (traverse ⦃ iTraversable ⦄ ⦃ iApplicativeStateL ⦄ (mkState ∘ flip f) t) s

mapAccumR : ⦃ Traversable t ⦄ → (s → a → s × b) → s → t a → s × t b
mapAccumR ⦃ iTraversable ⦄ f s t = State.run (traverse ⦃ iTraversable ⦄ ⦃ iApplicativeStateR ⦄ (mkState ∘ flip f) t) s

mapAccumM : ⦃ Monad m ⦄ → ⦃ Traversable t ⦄ → (s → a → m (s × b)) → s → t a → m (s × t b)
mapAccumM f s t = StateT.run (mapM (mkStateT ∘ flip f) t) s

forAccumM : ⦃ Monad m ⦄ → ⦃ Traversable t ⦄ → s → t a → (s → a → m (s × b)) → m (s × t b)
forAccumM s t f = mapAccumM f s t

-- Omitted for now:
-- - 'fmapDefault :: Traversable t => (a -> b) -> t a -> t b'
-- - 'foldMapDefault :: (Traversable t, Monoid m) => (a -> m) -> t a -> m'
