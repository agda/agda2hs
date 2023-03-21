module Haskell.Law.Ord.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Maybe
open import Haskell.Prim.Ord

open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Maybe
open import Haskell.Law.Ord.Def

postulate compMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → (x <= y || y <= x) ≡ True

postulate transMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrd : IsLawfulOrd a ⦄ → ∀ ( x y z : Maybe a ) → ((x <= y) && (y <= z)) ≡ True → (x <= z) ≡ True

reflMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrdA : IsLawfulOrd a ⦄
  → ∀ (x : Maybe a) → (x <= x) ≡ True
reflMaybe Nothing = refl
reflMaybe {{ iLawfulOrdA = lOrd }} (Just x) 
  = cong (λ eq → eq /= GT)
    (equality (compare x x) EQ (trans (sym (IsLawfulOrd.compareEq lOrd x x)) (eqReflexivity x)))

postulate antisymmetryMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → ((x <= y) && (y <= x)) ≡ True → (x == y) ≡ True

postulate lte2gteMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → (x >= y) ≡ (y <= x)

postulate lNotLteNeqMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → (x < y) ≡ (x <= y && x /= y)

postulate lt2gtMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → (x > y) ≡ (y < x)

compareLtMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x < y) ≡ (compare x y == LT)
compareLtMaybe Nothing  Nothing  = refl
compareLtMaybe Nothing  (Just _) = refl
compareLtMaybe (Just _) Nothing  = refl
compareLtMaybe (Just _) (Just _) = refl

compareGtMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x > y) ≡ (compare x y == GT)
compareGtMaybe Nothing  Nothing  = refl
compareGtMaybe Nothing  (Just _) = refl
compareGtMaybe (Just _) Nothing  = refl
compareGtMaybe (Just _) (Just _) = refl

compareEqMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrdA : IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x == y) ≡ (compare x y == EQ)
compareEqMaybe Nothing  Nothing  = refl
compareEqMaybe Nothing  (Just y) = refl
compareEqMaybe (Just x) Nothing  = refl
compareEqMaybe {{ iLawfulOrdA = lOrd }} (Just x) (Just y) = IsLawfulOrd.compareEq lOrd x y

postulate min2ifMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → ((min x y) == (if (x <= y) then x else y)) ≡ True

postulate max2ifMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → ((max x y) == (if (x >= y) then x else y)) ≡ True

instance
  iLawfulOrdMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → IsLawfulOrd (Maybe a)
  iLawfulOrdMaybe = λ where
    .comparability → compMaybe
    .transitivity → transMaybe
    .reflexivity → reflMaybe
    .antisymmetry → antisymmetryMaybe
    .lte2gte → lte2gteMaybe
    .lNotLteNeq → lNotLteNeqMaybe
    .lt2gt → lt2gtMaybe
    .compareLt → compareLtMaybe
    .compareGt → compareGtMaybe
    .compareEq → compareEqMaybe
    .min2if → min2ifMaybe
    .max2if → max2ifMaybe
   