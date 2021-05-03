
module Haskell.Prim.Traversable where

open import Haskell.Prim
open import Haskell.Prim.Applicative
open import Haskell.Prim.Functor
open import Haskell.Prim.Foldable
open import Haskell.Prim.Monad
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple

--------------------------------------------------
-- Traversable

record Traversable (t : Set → Set) : Set₁ where
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

open Traversable ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Traversable existing-class #-}

instance
  iTraversableList : Traversable List
  iTraversableList .traverse f []       = pure []
  iTraversableList .traverse f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈

  iTraversableMaybe : Traversable Maybe
  iTraversableMaybe .traverse f Nothing  = pure Nothing
  iTraversableMaybe .traverse f (Just x) = Just <$> f x

  iTraversableEither : Traversable (Either a)
  iTraversableEither .traverse f (Left  x) = pure (Left x)
  iTraversableEither .traverse f (Right y) = Right <$> f y

  iTraversablePair : Traversable (a ×_)
  iTraversablePair .traverse f (x , y) = (x ,_) <$> f y
