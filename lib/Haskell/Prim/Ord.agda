
module Haskell.Prim.Ord where

open import Agda.Builtin.Nat as Nat hiding (_==_; _<_)
open import Agda.Builtin.Char

open import Haskell.Prim
open import Haskell.Prim.Eq
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

--------------------------------------------------
-- Ordering

data Ordering : Set where
  LT EQ GT : Ordering

instance
  iEqOrdering : Eq Ordering
  iEqOrdering ._==_ LT LT = true
  iEqOrdering ._==_ EQ EQ = true
  iEqOrdering ._==_ GT GT = true
  iEqOrdering ._==_ _  _  = false

  iSemigroupOrdering : Semigroup Ordering
  iSemigroupOrdering ._<>_ LT _ = LT
  iSemigroupOrdering ._<>_ EQ o = o
  iSemigroupOrdering ._<>_ GT _ = GT

  iMonoidOrdering : Monoid Ordering
  iMonoidOrdering .mempty = EQ

--------------------------------------------------
-- Ord

record Ord (a : Set) : Set where
  field
    compare : a → a → Ordering
    _<_  : a → a → Bool
    _>_  : a → a → Bool
    _>=_ : a → a → Bool
    _<=_ : a → a → Bool
    max  : a → a → a
    min  : a → a → a
    overlap ⦃ super ⦄ : Eq a

  infix 4 _<_ _>_ _<=_ _>=_

open Ord ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Ord existing-class #-}

ordFromCompare : ⦃ Eq a ⦄ → (a → a → Ordering) → Ord a
ordFromCompare cmp .compare = cmp
ordFromCompare cmp ._<_  x y = cmp x y == LT
ordFromCompare cmp ._>_  x y = cmp x y == GT
ordFromCompare cmp ._<=_ x y = cmp x y /= GT
ordFromCompare cmp ._>=_ x y = cmp x y /= LT
ordFromCompare cmp .max  x y = if cmp x y == LT then y else x
ordFromCompare cmp .min  x y = if cmp x y == GT then y else x

ordFromLessThan : ⦃ Eq a ⦄ → (a → a → Bool) → Ord a
ordFromLessThan _<_ .compare x y = if x < y then LT else if x == y then EQ else GT
ordFromLessThan _<_ ._<_  x y = x < y
ordFromLessThan _<_ ._>_  x y = y < x
ordFromLessThan _<_ ._<=_ x y = x < y || x == y
ordFromLessThan _<_ ._>=_ x y = y < x || x == y
ordFromLessThan _<_ .max  x y = if x < y then y else x
ordFromLessThan _<_ .min  x y = if y < x then y else x

ordFromLessEq : ⦃ Eq a ⦄ → (a → a → Bool) → Ord a
ordFromLessEq _<=_ .compare x y = if x == y then EQ else if x <= y then LT else GT
ordFromLessEq _<=_ ._<_  x y = x <= y && not (x == y)
ordFromLessEq _<=_ ._>_  x y = y <= x && not (x == y)
ordFromLessEq _<=_ ._<=_ x y = x <= y
ordFromLessEq _<=_ ._>=_ x y = y <= x
ordFromLessEq _<=_ .max  x y = if y <= x then x else y
ordFromLessEq _<=_ .min  x y = if x <= y then x else y

private
  compareFromLt : ⦃ Eq a ⦄ → (a → a → Bool) → a → a → Ordering
  compareFromLt _<_ x y = if x < y then LT else if x == y then EQ else GT

instance
  iOrdNat : Ord Nat
  iOrdNat = ordFromLessThan Nat._<_

  iOrdInteger : Ord Integer
  iOrdInteger = ordFromLessThan ltInteger

  iOrdInt : Ord Int
  iOrdInt = ordFromLessThan ltInt

  iOrdWord : Ord Word
  iOrdWord = ordFromLessThan ltWord

  iOrdDouble : Ord Double
  iOrdDouble = ordFromLessThan primFloatNumericalLess

  iOrdChar : Ord Char
  iOrdChar = ordFromLessThan λ x y → primCharToNat x < primCharToNat y

  iOrdBool : Ord Bool
  iOrdBool = ordFromCompare λ where
    false true  → LT
    true  false → GT
    _     _     → EQ

  iOrdTuple₀ : Ord (Tuple [])
  iOrdTuple₀ = ordFromCompare λ _ _ → EQ

  iOrdTuple : ∀ {as} → ⦃ Ord a ⦄ → ⦃ Ord (Tuple as) ⦄ → Ord (Tuple (a ∷ as))
  iOrdTuple = ordFromCompare λ where (x ∷ xs) (y ∷ ys) → compare x y <> compare xs ys

compareList : ⦃ Ord a ⦄ → List a → List a → Ordering
compareList []       []       = EQ
compareList []       (_ ∷ _)  = LT
compareList (_ ∷ _)  []       = GT
compareList (x ∷ xs) (y ∷ ys) = compare x y <> compareList xs ys

instance
  iOrdList : ⦃ Ord a ⦄ → Ord (List a)
  iOrdList = ordFromCompare compareList

  iOrdMaybe : ⦃ Ord a ⦄ → Ord (Maybe a)
  iOrdMaybe = ordFromCompare λ where
    Nothing  Nothing  → EQ
    Nothing  (Just _) → LT
    (Just _) Nothing  → GT
    (Just x) (Just y) → compare x y

  iOrdEither : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → Ord (Either a b)
  iOrdEither = ordFromCompare λ where
    (Left  x) (Left  y) → compare x y
    (Left  _) (Right _) → LT
    (Right _) (Left  _) → GT
    (Right x) (Right y) → compare x y

  iOrdOrdering : Ord Ordering
  iOrdOrdering = ordFromCompare λ where
    LT LT → EQ
    LT _  → LT
    _  LT → GT
    EQ EQ → EQ
    EQ GT → LT
    GT EQ → GT
    GT GT → EQ
