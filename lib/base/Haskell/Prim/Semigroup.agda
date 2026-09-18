module Haskell.Prim.Semigroup where

open import Haskell.Prim
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple


--------------------------------------------------------------------------------
-- Semigroup

-- ** base
record Semigroup (a : Type) : Type where
  infixr 6 _<>_
  field _<>_ : a → a → a

-- ** export
open Semigroup ⦃...⦄ public
{-# COMPILE AGDA2HS Semigroup existing-class #-}

-- ** instances
module Instances where
  instance
    iSemigroupList : Semigroup (List a)
    iSemigroupList ._<>_ = _++_

    iSemigroupMaybe : ⦃ Semigroup a ⦄ → Semigroup (Maybe a)
    iSemigroupMaybe ._<>_          Nothing m = m
    iSemigroupMaybe ._<>_ m        Nothing   = m
    iSemigroupMaybe ._<>_ (Just x) (Just y)  = Just (x <> y)

    iSemigroupEither : Semigroup (Either a b)
    iSemigroupEither ._<>_ (Left _) e = e
    iSemigroupEither ._<>_ e        _ = e

    iSemigroupFun : ⦃ Semigroup b ⦄ → Semigroup (a → b)
    iSemigroupFun ._<>_ f g x = f x <> g x

    iSemigroupUnit : Semigroup ⊤
    iSemigroupUnit ._<>_ _ _ = tt

    iSemigroupTuple₂ : ⦃ Semigroup a ⦄ → ⦃ Semigroup b ⦄ → Semigroup (a × b)
    iSemigroupTuple₂ ._<>_ (x₁ , y₁) (x₂ , y₂) = x₁ <> x₂ , y₁ <> y₂

    iSemigroupTuple₃ : ⦃ Semigroup a ⦄ → ⦃ Semigroup b ⦄ → ⦃ Semigroup c ⦄ → Semigroup (a × b × c)
    iSemigroupTuple₃ ._<>_ (x₁ , y₁ , z₁) (x₂ , y₂ , z₂) = x₁ <> x₂ , y₁ <> y₂ , z₁ <> z₂
open Instances public
