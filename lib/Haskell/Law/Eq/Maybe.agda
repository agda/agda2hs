module Haskell.Law.Eq.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Maybe

open import Haskell.Law.Equality
open import Haskell.Law.Maybe
open import Haskell.Law.Eq.Def

equalityMaybe : ⦃ iEqA : Eq a ⦄ → ⦃ iLawfulEq : IsLawfulEq a ⦄
  → ∀ (x y : Maybe a) → (x == y) ≡ True → x ≡ y
equalityMaybe Nothing Nothing _ = refl
equalityMaybe {{ iLawfulEq = lEq }} (Just x) (Just y) h
  = cong Just (IsLawfulEq.equality lEq x y h)

nequalityMaybe : ⦃ iEqA : Eq a ⦄ → ⦃ iLawfulEq : IsLawfulEq a ⦄
  → ∀ (x y : Maybe a) → (x == y) ≡ False → (x ≡ y → ⊥)
nequalityMaybe Nothing Nothing ()
nequalityMaybe Nothing (Just y) h = λ()
nequalityMaybe (Just x) Nothing h = λ()
nequalityMaybe {{ iLawfulEq = lEq }} (Just x) (Just y) h 
  = λ eq → (IsLawfulEq.nequality lEq x y h) (injective eq)

instance
  iLawfulEqMaybe : ⦃ iEqA : Eq a ⦄ → ⦃ iLawfulEq : IsLawfulEq a ⦄ → IsLawfulEq (Maybe a)
  iLawfulEqMaybe = λ where
    .equality → equalityMaybe
    .nequality → nequalityMaybe
 