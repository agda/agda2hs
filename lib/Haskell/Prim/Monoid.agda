
module Haskell.Prim.Monoid where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple

--------------------------------------------------
-- Semigroup

record Semigroup (a : Set) : Set where
  infixr 6 _<>_
  field _<>_ : a → a → a
open Semigroup ⦃...⦄ public
{-# COMPILE AGDA2HS Semigroup existing-class #-}

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


--------------------------------------------------
-- Monoid

-- ** base
record Monoid (a : Set) : Set where
  field
    mempty : a
    overlap ⦃ super ⦄ : Semigroup a
    mappend : a → a → a
    mconcat : List a → a
-- ** defaults
record DefaultMonoid (a : Set) : Set where
  field
    mempty : a
    overlap ⦃ super ⦄ : Semigroup a

  mappend : a → a → a
  mappend = _<>_

  mconcat : List a → a
  mconcat []       = mempty
  mconcat (x ∷ xs) = x <> mconcat xs
-- ** export
open Monoid ⦃...⦄ public
{-# COMPILE AGDA2HS Monoid existing-class #-}
-- ** instances
private
  infix 0 mempty=_
  mempty=_ : ⦃ Semigroup a ⦄ → a → Monoid a
  mempty= x = record {DefaultMonoid (record {mempty = x})}

  mkMonoid : DefaultMonoid a → Monoid a
  mkMonoid x = record {DefaultMonoid x}
instance
  iMonoidList : Monoid (List a)
  iMonoidList = mempty= []

  iMonoidMaybe : ⦃ Semigroup a ⦄ → Monoid (Maybe a)
  iMonoidMaybe = mempty= Nothing

  iMonoidFun : ⦃ Monoid b ⦄ → Monoid (a → b)
  iMonoidFun = mempty= λ _ → mempty

  iMonoidUnit : Monoid ⊤
  iMonoidUnit = mempty= tt

  iMonoidTuple₂ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monoid (a × b)
  iMonoidTuple₂ = mempty= (mempty , mempty)

  iMonoidTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →  Monoid (a × b × c)
  iMonoidTuple₃ = mempty= (mempty , mempty , mempty)

open DefaultMonoid

MonoidEndo : Monoid (a → a)
MonoidEndo = mkMonoid λ where
  .mempty → id
  .super ._<>_ → _∘_

MonoidEndoᵒᵖ : Monoid (a → a)
MonoidEndoᵒᵖ = mkMonoid λ where
  .mempty      → id
  .super ._<>_ → flip _∘_

MonoidConj : Monoid Bool
MonoidConj = mkMonoid λ where
  .mempty      → True
  .super ._<>_ → _&&_

MonoidDisj : Monoid Bool
MonoidDisj = mkMonoid λ where
  .mempty      → False
  .super ._<>_ → _||_
