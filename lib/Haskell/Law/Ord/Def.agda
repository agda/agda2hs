module Haskell.Law.Ord.Def where

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Double
open import Haskell.Prim.Tuple
open import Haskell.Prim.Monoid
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either

open import Haskell.Prim.Eq
open import Haskell.Law.Eq

open import Haskell.Law.Bool
open import Haskell.Law.Equality

record IsLawfulOrd (a : Set) ⦃ iOrd : Ord a ⦄ : Set₁ where
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
    lte2gte : ∀ (x y : a) → (x <= y) ≡ (y >= x)

    -- x < y = x <= y && x /= y
    lt2LteNeq : ∀ (x y : a) → (x < y) ≡ (x <= y && x /= y)

    -- x > y = y < x
    lt2gt : ∀ (x y : a) → (x < y) ≡ (y > x)

    -- x < y = compare x y == LT
    compareLt : ∀ (x y : a) → (x < y) ≡ (compare x y == LT)

    -- x > y = compare x y == GT
    compareGt : ∀ (x y : a) → (x > y) ≡ (compare x y == GT)

    -- x == y = compare x y == EQ
    compareEq : ∀ (x y : a) → (x == y) ≡ (compare x y == EQ)

    -- min x y == if x <= y then x else y = True
    min2if : ∀ (x y : a) → ((min x y) == (if (x <= y) then x else y)) ≡ True

    -- max x y == if x >= y then x else y = True
    max2if : ∀ (x y : a) → ((max x y) == (if (x >= y) then x else y)) ≡ True

open IsLawfulOrd ⦃ ... ⦄ public

--------------------------------------------------
-- Some more helper laws

eq2nlt : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x == y) ≡ True → (x < y) ≡ False
eq2nlt x y h
  rewrite compareEq x y
    | compareLt x y
    | equality (compare x y) EQ h
  = refl

eq2ngt : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x == y) ≡ True → (x > y) ≡ False
eq2ngt x y h
  rewrite compareEq x y
    | compareGt x y
    | equality (compare x y) EQ h
  = refl

lte2LtEq : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x <= y) ≡ (x < y || x == y)
lte2LtEq x y 
  rewrite lt2LteNeq x y
    with (x <= y) in h₁ | (x == y) in h₂
...| True | True  = refl
...| True | False = refl
...| False | True 
  rewrite equality x y h₂ | sym $ h₁ 
  = reflexivity y
...| False | False = refl

gte2GtEq : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x >= y) ≡ (x > y || x == y)
gte2GtEq x y
  rewrite sym $ lte2gte y x
    | lte2LtEq y x
    | eqSymmetry y x
    | lt2gt y x
  = refl

gte2nlt : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x >= y) ≡ not (x < y)
gte2nlt x y
  rewrite gte2GtEq x y
    | compareGt x y
    | compareEq x y
    | compareLt x y
  with compare x y
... | GT = refl 
... | EQ = refl 
... | LT = refl 

gte2nLT : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x >= y) ≡ (compare x y /= LT)
gte2nLT x y
  rewrite gte2nlt x y
    | compareLt x y
  = refl

lte2ngt : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x <= y) ≡ not (x > y)
lte2ngt x y
  rewrite lte2LtEq x y
    | compareLt x y
    | compareEq x y
    | compareGt x y
  with compare x y
... | GT = refl 
... | EQ = refl 
... | LT = refl 

lte2nGT : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x <= y) ≡ (compare x y /= GT)
lte2nGT x y
  rewrite lte2ngt x y
    | compareGt x y
  = refl

eq2lte : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x == y) ≡ True → (x <= y) ≡ True
eq2lte x y h
  rewrite lte2ngt x y
    | eq2ngt x y h
  = refl

lt2lte : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x < y) ≡ True → (x <= y) ≡ True
lt2lte x y h = &&-rightTrue' (x < y) (x <= y) (x /= y) (lt2LteNeq x y) h

eq2gte : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x == y) ≡ True → (x >= y) ≡ True
eq2gte x y h
  rewrite gte2nlt x y
    | eq2nlt x y h
  = refl

gt2gte : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x > y) ≡ True → (x >= y) ≡ True
gt2gte x y h
  rewrite sym (lt2gt y x)
    | sym (lt2lte y x h)
    | lte2gte y x
  = refl

reverseLte : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  →  ∀ ( a b c d : a ) → 
  ((a <= b) && (c <= d)) ≡ (( d >= c) && (b >= a))
reverseLte a b c d 
  rewrite &&-sym (a <= b) (c <= d)
  | sym $ lte2gte c d 
  | sym $ lte2gte a b  
  = refl

--------------------------------------------------
-- Postulated instances

postulate instance

  iLawfulOrdDouble : IsLawfulOrd Double

  iLawfulOrdChar : IsLawfulOrd Char

  iLawfulOrdUnit : IsLawfulOrd ⊤

  iLawfulOrdTuple₂ : ⦃ iOrdA : Ord a ⦄ ⦃ iOrdB : Ord b ⦄
                   → ⦃ IsLawfulOrd a ⦄ → ⦃ IsLawfulOrd b ⦄
                   → IsLawfulOrd (a × b)

  iLawfulOrdTuple₃ : ⦃ iOrdA : Ord a ⦄ ⦃ iOrdB : Ord b ⦄ ⦃ iOrdC : Ord c ⦄
                   → ⦃ IsLawfulOrd a ⦄ → ⦃ IsLawfulOrd b ⦄ → ⦃ IsLawfulOrd c ⦄
                   → IsLawfulOrd (a × b × c)

  iLawfulOrdList : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄ → IsLawfulOrd (List a)

  iLawfulOrdEither : ⦃ iOrdA : Ord a ⦄ → ⦃ iOrdB : Ord b ⦄ →  ⦃ IsLawfulOrd a ⦄ → ⦃ IsLawfulOrd b ⦄ → IsLawfulOrd (Either a b)
