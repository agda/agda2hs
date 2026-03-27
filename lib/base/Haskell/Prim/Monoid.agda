module Haskell.Prim.Monoid where

open import Haskell.Prim
open import Haskell.Prim.Semigroup
  renaming (module Instances to SemigroupInstances)
open import Haskell.Prim.Bool
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple


--------------------------------------------------------------------------------
-- Monoid

-- ** base
record Monoid (a : Type) : Type where
  field
    mempty : a
    overlap ⦃ super ⦄ : Semigroup a
    mappend : a → a → a
    mconcat : List a → a

-- ** defaults
record DefaultMonoid (a : Type) : Type where
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
module Instances where
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
open Instances public

open DefaultMonoid

MonoidEndo : Monoid (a → a)
MonoidEndo = record {DefaultMonoid (λ where
  .mempty      → id
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

MonoidFirst : Monoid (Maybe a)
MonoidFirst = record {DefaultMonoid (λ where
  .mempty      → Nothing
  .super ._<>_ → λ where
    Nothing b → b
    a       _ → a)}

MonoidLast : Monoid (Maybe a)
MonoidLast = record {DefaultMonoid (λ where
  .mempty      → Nothing
  .super ._<>_ → λ where
    a Nothing → a
    _       b → b)}
