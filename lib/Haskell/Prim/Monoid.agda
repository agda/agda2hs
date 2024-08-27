
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
instance
  iDefaultMonoidList : DefaultMonoid (List a)
  iDefaultMonoidList .DefaultMonoid.mempty = []

  iMonoidList : Monoid (List a)
  iMonoidList = record{DefaultMonoid iDefaultMonoidList}

  iDefaultMonoidMaybe : ⦃ Semigroup a ⦄ → DefaultMonoid (Maybe a)
  iDefaultMonoidMaybe .DefaultMonoid.mempty = Nothing

  iMonoidMaybe : ⦃ Semigroup a ⦄ → Monoid (Maybe a)
  iMonoidMaybe = record{DefaultMonoid iDefaultMonoidMaybe}

  iDefaultMonoidFun : ⦃ Monoid b ⦄ → DefaultMonoid (a → b)
  iDefaultMonoidFun .DefaultMonoid.mempty = λ _ → mempty

  iMonoidFun : ⦃ Monoid b ⦄ → Monoid (a → b)
  iMonoidFun = record{DefaultMonoid iDefaultMonoidFun}

  iDefaultMonoidUnit : DefaultMonoid ⊤
  iDefaultMonoidUnit .DefaultMonoid.mempty = tt

  iMonoidUnit : Monoid ⊤
  iMonoidUnit = record{DefaultMonoid iDefaultMonoidUnit}

  iDefaultMonoidTuple₂ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → DefaultMonoid (a × b)
  iDefaultMonoidTuple₂ .DefaultMonoid.mempty = (mempty , mempty)

  iMonoidTuple₂ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monoid (a × b)
  iMonoidTuple₂ = record{DefaultMonoid iDefaultMonoidTuple₂}

  iDefaultMonoidTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ → DefaultMonoid (a × b × c)
  iDefaultMonoidTuple₃ .DefaultMonoid.mempty = (mempty , mempty , mempty)

  iMonoidTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →  Monoid (a × b × c)
  iMonoidTuple₃ = record{DefaultMonoid iDefaultMonoidTuple₃}

open DefaultMonoid

MonoidEndo : Monoid (a → a)
MonoidEndo = record {DefaultMonoid (λ where
      .mempty → id
      .super ._<>_ → _∘_)}

MonoidEndoᵒᵖ : Monoid (a → a)
MonoidEndoᵒᵖ = record {DefaultMonoid (λ where
  .mempty      → id
  .super ._<>_ → flip _∘_) }

MonoidConj : Monoid Bool
MonoidConj = record {DefaultMonoid (λ where
  .mempty      → True
  .super ._<>_ → _&&_)}

MonoidDisj : Monoid Bool
MonoidDisj = record {DefaultMonoid (λ where
  .mempty      → False
  .super ._<>_ → _||_)}
