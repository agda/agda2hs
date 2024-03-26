module Haskell.Law.Ord.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Maybe
open import Haskell.Prim.Ord

open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Equality hiding ( trustMe )
open import Haskell.Law.Maybe
open import Haskell.Law.Ord.Def

compMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x <= y || y <= x) ≡ True
compMaybe Nothing  Nothing  = refl
compMaybe Nothing  (Just _) = refl
compMaybe (Just _) Nothing  = refl
compMaybe (Just x) (Just y)
  rewrite sym (lte2nGT x y)
    | sym (lte2nGT y x)
  = comparability x y

transMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ ( x y z : Maybe a ) → ((x <= y) && (y <= z)) ≡ True → (x <= z) ≡ True
transMaybe Nothing  Nothing  Nothing  _ = refl
transMaybe Nothing  Nothing  (Just _) _ = refl
transMaybe Nothing  (Just _) (Just _) _ = refl
transMaybe (Just x) (Just y) Nothing  h 
  = magic (nequality refl (&&-rightTrue {b = Just y <= Nothing} h))
transMaybe (Just x) (Just y) (Just z) h
  rewrite sym (compareGt x z)
    | sym (lte2nGT x y)
    | sym (lte2nGT y z)
    | sym (lte2ngt x z) -- not (x > z) → (x <= z)
  = transitivity x y z h

reflMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x : Maybe a) → (x <= x) ≡ True
reflMaybe Nothing = refl
reflMaybe (Just x) = cong (λ eq → eq /= GT) (compareSelf x)

antisymmetryMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → ((x <= y) && (y <= x)) ≡ True → (x == y) ≡ True
antisymmetryMaybe Nothing  Nothing  _ = refl
antisymmetryMaybe (Just x) (Just y) h
  rewrite sym (lte2nGT x y)
    | sym (lte2nGT y x)
  = antisymmetry x y h

lte2gteMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x <= y) ≡ (y >= x)
lte2gteMaybe Nothing  Nothing  = refl
lte2gteMaybe Nothing  (Just _) = refl
lte2gteMaybe (Just _) Nothing  = refl
lte2gteMaybe (Just x) (Just y)
  rewrite sym (compareGt x y)
    | sym (lte2ngt x y)
    | lte2gte x y -- IH
    | gte2nlt y x
    | compareLt y x
  = refl

lt2LteNeqMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x < y) ≡ (x <= y && x /= y)
lt2LteNeqMaybe Nothing  Nothing  = refl
lt2LteNeqMaybe Nothing  (Just _) = refl
lt2LteNeqMaybe (Just _) Nothing  = refl
lt2LteNeqMaybe (Just x) (Just y)
  rewrite sym (compareLt x y)
    | lt2LteNeq x y -- IH
    | lte2ngt x y
    | compareGt x y
  = refl

lt2gtMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → (x < y) ≡ (y > x)
lt2gtMaybe Nothing  Nothing  = refl
lt2gtMaybe Nothing  (Just _) = refl
lt2gtMaybe (Just _) Nothing  = refl
lt2gtMaybe (Just x) (Just y)
  rewrite sym (compareLt x y)
    | lt2gt x y -- IH
    | compareGt y x
  = refl

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
compareEqMaybe (Just x) (Just y) = compareEq x y

min2ifMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → ((min x y) == (if (x <= y) then x else y)) ≡ True
min2ifMaybe Nothing  Nothing  = refl
min2ifMaybe Nothing  (Just _) = refl
min2ifMaybe (Just _) Nothing = refl
min2ifMaybe (Just x) (Just y)
  rewrite ifFlip (compare x y == GT) {Just y} {Just x}
  = equality'
      {x = if (compare x y /= GT) then Just x else Just y}
      {y = if (compare x y /= GT) then Just x else Just y}
      refl

max2ifMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : Maybe a) → ((max x y) == (if (x >= y) then x else y)) ≡ True
max2ifMaybe Nothing  Nothing  = refl
max2ifMaybe Nothing  (Just y) = eqReflexivity y
max2ifMaybe (Just x) Nothing  = eqReflexivity x
max2ifMaybe (Just x) (Just y)
  rewrite ifFlip (compare x y == LT) {Just y} {Just x}
  = equality'
    {x = if (compare x y /= LT) then Just x else Just y}
    {y = if (compare x y /= LT) then Just x else Just y}
    refl

instance
  iLawfulOrdMaybe : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → IsLawfulOrd (Maybe a)
  iLawfulOrdMaybe = λ where
    .comparability → compMaybe
    .transitivity → transMaybe
    .reflexivity → reflMaybe
    .antisymmetry → antisymmetryMaybe
    .lte2gte → lte2gteMaybe
    .lt2LteNeq → lt2LteNeqMaybe
    .lt2gt → lt2gtMaybe
    .compareLt → compareLtMaybe
    .compareGt → compareGtMaybe
    .compareEq → compareEqMaybe
    .min2if → min2ifMaybe
    .max2if → max2ifMaybe

