
module Haskell.Prim.Monoid where

open import Agda.Builtin.Unit

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
  field
    _<>_ : a → a → a

open Semigroup ⦃ ... ⦄ public

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

  iSemigroupTuple₀ : Semigroup (Tuple [])
  iSemigroupTuple₀ ._<>_ _ _ = []

  iSemigroupTuple : ∀ {as} → ⦃ Semigroup a ⦄ → ⦃ Semigroup (Tuple as) ⦄ → Semigroup (Tuple (a ∷ as))
  iSemigroupTuple ._<>_ (x ∷ xs) (y ∷ ys) = x <> y ∷ xs <> ys


--------------------------------------------------
-- Monoid

record Monoid (a : Set) : Set where
  field
    mempty : a
    overlap ⦃ super ⦄ : Semigroup a

  mappend : a → a → a
  mappend = _<>_

  mconcat : List a → a
  mconcat []       = mempty
  mconcat (x ∷ xs) = x <> mconcat xs

open Monoid ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Monoid existing-class #-}

instance
  iMonoidList : Monoid (List a)
  iMonoidList .mempty = []

  iMonoidMaybe : ⦃ Semigroup a ⦄ → Monoid (Maybe a)
  iMonoidMaybe .mempty = Nothing

  iMonoidFun : ⦃ Monoid b ⦄ → Monoid (a → b)
  iMonoidFun .mempty _ = mempty

  iMonoidUnit : Monoid ⊤
  iMonoidUnit .mempty = tt

  iMonoidTuple₀ : Monoid (Tuple [])
  iMonoidTuple₀ .mempty = []

  iMonoidTuple : ∀ {as} → ⦃ Monoid a ⦄ → ⦃ Monoid (Tuple as) ⦄ → Monoid (Tuple (a ∷ as))
  iMonoidTuple .mempty = mempty ∷ mempty

MonoidEndo : Monoid (a → a)
MonoidEndo .mempty      = id
MonoidEndo .super ._<>_ = _∘_

MonoidEndoᵒᵖ : Monoid (a → a)
MonoidEndoᵒᵖ .mempty      = id
MonoidEndoᵒᵖ .super ._<>_ = flip _∘_

MonoidConj : Monoid Bool
MonoidConj .mempty      = true
MonoidConj .super ._<>_ = _&&_

MonoidDisj : Monoid Bool
MonoidDisj .mempty      = false
MonoidDisj .super ._<>_ = _||_
