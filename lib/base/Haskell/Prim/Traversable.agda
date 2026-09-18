module Haskell.Prim.Traversable where

open import Haskell.Prim
open import Haskell.Prim.Functor
  renaming (module Instances to FunctorInstances)
open import Haskell.Prim.Applicative
  renaming (module Instances to ApplicativeInstances)
open import Haskell.Prim.Monad
  renaming (module Instances to MonadInstances)
open import Haskell.Prim.Foldable
  renaming (module Instances to FoldableInstances)
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple


--------------------------------------------------------------------------------
-- Traversable

-- ** base
record Traversable (t : Type → Type) : Type₁ where
  field
    traverse : ⦃ Applicative f ⦄ → (a → f b) → t a → f (t b)
    overlap ⦃ functor ⦄ : Functor t
    overlap ⦃ foldable ⦄ : Foldable t

    sequenceA : ⦃ Applicative f ⦄ → t (f a) → f (t a)
    mapM : ⦃ Monad m ⦄ → (a → m b) → t a → m (t b)
    sequence : ⦃ Monad m ⦄ → t (m a) → m (t a)

-- ** defaults
record DefaultTraversable (t : Type → Type) : Type₁ where
  field
    traverse : ⦃ Applicative f ⦄ → (a → f b) → t a → f (t b)
    overlap ⦃ functor ⦄ : Functor t
    overlap ⦃ foldable ⦄ : Foldable t

  sequenceA : ⦃ Applicative f ⦄ → t (f a) → f (t a)
  sequenceA = traverse id

  mapM : ⦃ Monad m ⦄ → (a → m b) → t a → m (t b)
  mapM = traverse

  sequence : ⦃ Monad m ⦄ → t (m a) → m (t a)
  sequence = sequenceA

-- ** export
open Traversable ⦃...⦄ public
{-# COMPILE AGDA2HS Traversable existing-class #-}

-- ** instances
module Instances where
  private
    mkTraversable : DefaultTraversable t → Traversable t
    mkTraversable x = record {DefaultTraversable x}

    infix 0 traverse=_
    traverse=_ : ⦃ Functor t ⦄ → ⦃ Foldable t ⦄
              → (∀ {f a b} → ⦃ Applicative f ⦄ → (a → f b) → t a → f (t b))
              → Traversable t
    traverse= x = record {DefaultTraversable (record {traverse = x})}

  instance
    open DefaultTraversable

    iTraversableList : Traversable List
    iTraversableList = traverse= traverseList
      where
        traverseList : ⦃ Applicative f ⦄ → (a → f b) → List a → f (List b)
        traverseList f []       = pure []
        traverseList f (x ∷ xs) = ⦇ f x ∷ traverseList f xs ⦈

    iTraversableMaybe : Traversable Maybe
    iTraversableMaybe = traverse= λ where
      f Nothing  → pure Nothing
      f (Just x) → fmap Just (f x)

    iTraversableEither : Traversable (Either a)
    iTraversableEither = traverse= λ where
      f (Left  x) → pure (Left x)
      f (Right y) → fmap Right (f y)

    iTraversablePair : Traversable (a ×_)
    iTraversablePair = traverse= λ
      f (x , y) → fmap (x ,_) (f y)
open Instances public
