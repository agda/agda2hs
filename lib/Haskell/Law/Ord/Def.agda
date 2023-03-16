module Haskell.Law.Ord.Def where

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Int
open import Haskell.Prim.Word
open import Haskell.Prim.Integer
open import Haskell.Prim.Double
open import Haskell.Prim.Tuple
open import Haskell.Prim.Monoid
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either

open import Haskell.Prim.Eq
open import Haskell.Law.Eq

open import Haskell.Law.Equality

record IsLawfulOrd (a : Set) {{iOrd : Ord a}} : Set₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulEq a

    -- Comparability: x <= y || y <= x = True
    comparability : ∀ (x y : a) → (x <= y || y <= x) ≡ True

    -- Transitivity: if x <= y && y <= z = True, then x <= z = True
    transitivity :  ∀ ( x y z : a ) → ((x <= y) && (y <= z)) ≡ True → (x <= z) ≡ True

    -- Reflexivity: x <= x = True
    reflexivity : ∀ (x : a) → (x <= x) ≡ True

    -- Antisymmetry: if x <= y && y <= x = True, then x == y = True
    antisymmetry : ∀ (x y : a) → ((x <= y) && (y <= x)) ≡ True → (x == y) ≡ True

    -- x >= y = y <= x
    lte2gte : ∀ (x y : a) → (x >= y) ≡ (y <= x)

    -- x < y = x <= y && x /= y
    lNotLteNeq : ∀ (x y : a) → (x < y) ≡ (x <= y && x /= y)

    -- x > y = y < x
    lt2gt : ∀ (x y : a) → (x > y) ≡ (y < x)

    -- x < y = compare x y == LT
    isCompareLt : ∀ (x y : a) → Reflects (compare x y ≡ LT) (x < y)

    -- x > y = compare x y == GT
    isCompareGt : ∀ (x y : a) → Reflects (compare x y ≡ GT) (x > y)

    -- x == y = compare x y == EQ
    isCompareEq : ∀ (x y : a) → Reflects (compare x y ≡ EQ) (x == y)

    -- min x y == if x <= y then x else y = True
    min2if : ∀ (x y : a) → ((min x y) == (if (x <= y) then x else y)) ≡ True

    -- max x y == if x >= y then x else y = True
    max2if : ∀ (x y : a) → ((max x y) == (if (x >= y) then x else y)) ≡ True

  compareLt : ∀ (x y : a) → (x < y) ≡ True → compare x y ≡ LT
  compareLt x y h = extractTrue ⦃ h ⦄ (isCompareLt x y)

  ncompareLt : ∀ (x y : a) → (x < y) ≡ False → (compare x y ≡ LT → ⊥)
  ncompareLt x y h = extractFalse ⦃ h ⦄ (isCompareLt x y)

  compareGt : ∀ (x y : a) → (x > y) ≡ True → compare x y ≡ GT
  compareGt x y h = extractTrue ⦃ h ⦄ (isCompareGt x y)

  ncompareGt : ∀ (x y : a) → (x > y) ≡ False → (compare x y ≡ GT → ⊥)
  ncompareGt x y h = extractFalse ⦃ h ⦄ (isCompareGt x y)

  compareEq : ∀ (x y : a) → (x == y) ≡ True → compare x y ≡ EQ
  compareEq x y h = extractTrue ⦃ h ⦄ (isCompareEq x y)

  ncompareEq : ∀ (x y : a) → (x == y) ≡ False → (compare x y ≡ EQ → ⊥)
  ncompareEq x y h = extractFalse ⦃ h ⦄ (isCompareEq x y)
        
open IsLawfulOrd ⦃ ... ⦄ public

instance
  postulate iLawfulOrdNat : IsLawfulOrd Nat

  postulate iLawfulOrdInteger : IsLawfulOrd Integer

  postulate iLawfulOrdInt : IsLawfulOrd Int

  postulate iLawfulOrdWord : IsLawfulOrd Word

  postulate iLawfulOrdDouble : IsLawfulOrd Double

  postulate iLawfulOrdChar : IsLawfulOrd Char

  postulate iLawfulOrdTuple₀ : IsLawfulOrd (Tuple [])

  postulate iLawfulOrdTuple : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrdA : Ord (Tuple as) ⦄ → ⦃ IsLawfulOrd a ⦄ → ⦃ IsLawfulOrd (Tuple as) ⦄ → IsLawfulOrd (Tuple (a ∷ as))

  postulate iLawfulOrdList : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → IsLawfulOrd (List a)

  postulate iLawfulOrdEither : ⦃ iOrdA : Ord a ⦄ → ⦃ iOrdB : Ord b ⦄ →  ⦃ IsLawfulOrd a ⦄ → ⦃ IsLawfulOrd b ⦄ → IsLawfulOrd (Either a b)
