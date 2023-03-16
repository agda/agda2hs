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

private
  reflectsJustEq : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrd : IsLawfulOrd a ⦄
    → ∀ (x y : a) → Reflects (compare (Just x) (Just y) ≡ EQ) ((Just x) == (Just y))
  reflectsJustEq ⦃ iLawfulOrd = lOrd ⦄ x y with (x == y) in h
  ... | True  = ofY (compareEq x y h)
  ... | False = ofN λ eq → (ncompareEq x y h) eq

postulate compMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → (x <= y || y <= x) ≡ True

postulate transMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrd : IsLawfulOrd a ⦄ → ∀ ( x y z : Maybe a ) → ((x <= y) && (y <= z)) ≡ True → (x <= z) ≡ True

reflMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrdA : IsLawfulOrd a ⦄
  → ∀ (x : Maybe a) → (x <= x) ≡ True
reflMaybe Nothing = refl
reflMaybe {{ iLawfulOrdA = lOrd }} (Just x) 
  = cong (λ eq → eq /= GT) (compareEq x x (eqReflexivity x))

postulate antisymmetryMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → ((x <= y) && (y <= x)) ≡ True → (x == y) ≡ True

postulate lte2gteMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → (x >= y) ≡ (y <= x)

postulate lNotLteNeqMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → ∀ (x y : Maybe a) → (x < y) ≡ (x <= y && x /= y)

lt2gtMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x > y) ≡ (y < x)
lt2gtMaybe Nothing  Nothing  = refl
lt2gtMaybe Nothing  (Just _) = refl
lt2gtMaybe (Just _) Nothing  = refl
lt2gtMaybe (Just x) (Just y) = {!   !}

isCompareLtMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → Reflects (compare x y ≡ LT) (x < y)
isCompareLtMaybe Nothing  Nothing  = ofN λ()
isCompareLtMaybe Nothing  (Just _) = ofY refl
isCompareLtMaybe (Just _) Nothing  = ofN λ()
isCompareLtMaybe (Just x) (Just y) 
  = IsLawfulEq.isEquality iLawfulEqOrdering (compare x y) LT

isCompareGtMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → Reflects (compare x y ≡ GT) (x > y)
isCompareGtMaybe Nothing  Nothing  = ofN λ()
isCompareGtMaybe Nothing  (Just _) = ofN λ()
isCompareGtMaybe (Just _) Nothing  = ofY refl
isCompareGtMaybe (Just x) (Just y) 
  = IsLawfulEq.isEquality iLawfulEqOrdering (compare x y) GT

isCompareEqMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → Reflects (compare x y ≡ EQ) (x == y)
isCompareEqMaybe Nothing  Nothing  = ofY refl
isCompareEqMaybe Nothing  (Just _) = ofN λ()
isCompareEqMaybe (Just _) Nothing  = ofN λ()
isCompareEqMaybe (Just x) (Just y) = reflectsJustEq x y

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
    .isCompareLt → isCompareLtMaybe
    .isCompareGt → isCompareGtMaybe
    .isCompareEq → isCompareEqMaybe
    .min2if → min2ifMaybe
    .max2if → max2ifMaybe
   