
module Haskell.Prim.Ord where

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

data Ordering : Type where
  LT EQ GT : Ordering

instance
  iEqOrdering : Eq Ordering
  iEqOrdering ._==_ LT LT = True
  iEqOrdering ._==_ EQ EQ = True
  iEqOrdering ._==_ GT GT = True
  iEqOrdering ._==_ _  _  = False

  iSemigroupOrdering : Semigroup Ordering
  iSemigroupOrdering ._<>_ LT _ = LT
  iSemigroupOrdering ._<>_ EQ o = o
  iSemigroupOrdering ._<>_ GT _ = GT

  iMonoidOrdering : Monoid Ordering
  iMonoidOrdering = record {DefaultMonoid (record {mempty = EQ})}

--------------------------------------------------
-- Ord

record Ord (a : Type) : Type where
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

record OrdFromCompare (a : Type) : Type where
  field
    compare : a → a → Ordering
    overlap ⦃ super ⦄ : Eq a

  _<_  : a → a → Bool
  x < y = compare x y == LT

  _>_  : a → a → Bool
  x > y = compare x y == GT

  _>=_ : a → a → Bool
  x >= y = compare x y /= LT

  _<=_ : a → a → Bool
  x <= y = compare x y /= GT

  max  : a → a → a
  max x y = if compare x y == LT then y else x

  min  : a → a → a
  min x y = if compare x y == GT then y else x

record OrdFromLessThan (a : Type) : Type where
  field
    _<_ : a → a → Bool
    overlap ⦃ super ⦄ : Eq a

  compare : a → a → Ordering
  compare x y = if x < y then LT else if x == y then EQ else GT

  _>_  : a → a → Bool
  x > y = y < x

  _>=_ : a → a → Bool
  x >= y = y < x || x == y

  _<=_ : a → a → Bool
  x <= y = x < y || x == y

  max  : a → a → a
  max x y = if x < y then y else x

  min  : a → a → a
  min x y = if y < x then y else x


open Ord ⦃...⦄ public

{-# COMPILE AGDA2HS Ord existing-class #-}

private
  compareFromLt : ⦃ Eq a ⦄ → (a → a → Bool) → a → a → Ordering
  compareFromLt _<_ x y = if x < y then LT else if x == y then EQ else GT

private
  maxNat : Nat → Nat → Nat
  maxNat zero    y       = y
  maxNat (suc x) zero    = suc x
  maxNat (suc x) (suc y) = suc (maxNat x y)

  minNat : Nat → Nat → Nat
  minNat zero    y       = zero
  minNat (suc x) zero    = zero
  minNat (suc x) (suc y) = suc (minNat x y)

instance
  iOrdFromLessThanNat : OrdFromLessThan Nat
  iOrdFromLessThanNat .OrdFromLessThan._<_ = ltNat

  iOrdNat : Ord Nat
  iOrdNat = record
    { OrdFromLessThan iOrdFromLessThanNat
    ; max = maxNat
    ; min = minNat
    }

  iOrdFromLessThanInteger : OrdFromLessThan Integer
  iOrdFromLessThanInteger .OrdFromLessThan._<_ = ltInteger

  iOrdInteger : Ord Integer
  iOrdInteger = record {OrdFromLessThan iOrdFromLessThanInteger}

  iOrdFromLessThanInt : OrdFromLessThan Int
  iOrdFromLessThanInt .OrdFromLessThan._<_ = ltInt

  iOrdInt : Ord Int
  iOrdInt = record {OrdFromLessThan iOrdFromLessThanInt}

  iOrdFromLessThanWord : OrdFromLessThan Word
  iOrdFromLessThanWord .OrdFromLessThan._<_ = ltWord

  iOrdWord : Ord Word
  iOrdWord = record {OrdFromLessThan iOrdFromLessThanWord}

  iOrdFromLessThanDouble : OrdFromLessThan Double
  iOrdFromLessThanDouble .OrdFromLessThan._<_ = primFloatLess

  iOrdDouble : Ord Double
  iOrdDouble = record {OrdFromLessThan iOrdFromLessThanDouble}

  iOrdFromLessThanChar : OrdFromLessThan Char
  iOrdFromLessThanChar .OrdFromLessThan._<_ x y = c2n x < c2n y

  iOrdChar : Ord Char
  iOrdChar = record {OrdFromLessThan iOrdFromLessThanChar}

  iOrdFromCompareBool : OrdFromCompare Bool
  iOrdFromCompareBool .OrdFromCompare.compare = λ where
    False True  → LT
    True  False → GT
    _     _     → EQ

  iOrdBool : Ord Bool
  iOrdBool = record {OrdFromCompare iOrdFromCompareBool}

  iOrdFromCompareUnit : OrdFromCompare ⊤
  iOrdFromCompareUnit .OrdFromCompare.compare = λ _ _ → EQ

  iOrdUnit : Ord ⊤
  iOrdUnit = record {OrdFromCompare iOrdFromCompareUnit}

  iOrdFromCompareTuple₂ : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → OrdFromCompare (a × b)
  iOrdFromCompareTuple₂ .OrdFromCompare.compare = λ where
    (x₁ , y₁) (x₂ , y₂) → compare x₁ x₂ <> compare y₁ y₂

  iOrdTuple₂ : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → Ord (a × b)
  iOrdTuple₂ = record {OrdFromCompare iOrdFromCompareTuple₂}

  iOrdFromCompareTuple₃ : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → ⦃ Ord c ⦄ → OrdFromCompare (a × b × c)
  iOrdFromCompareTuple₃ .OrdFromCompare.compare = λ where
    (x₁ , y₁ , z₁) (x₂ , y₂ , z₂) → compare x₁ x₂ <> compare y₁ y₂ <> compare z₁ z₂

  iOrdTuple₃ : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → ⦃ Ord c ⦄ → Ord (a × b × c)
  iOrdTuple₃ = record {OrdFromCompare iOrdFromCompareTuple₃}

compareList : ⦃ Ord a ⦄ → List a → List a → Ordering
compareList []       []       = EQ
compareList []       (_ ∷ _)  = LT
compareList (_ ∷ _)  []       = GT
compareList (x ∷ xs) (y ∷ ys) = compare x y <> compareList xs ys

instance
  iOrdFromCompareList : ⦃ Ord a ⦄ → OrdFromCompare (List a)
  iOrdFromCompareList .OrdFromCompare.compare = compareList

  iOrdList : ⦃ Ord a ⦄ → Ord (List a)
  iOrdList = record {OrdFromCompare iOrdFromCompareList}

  iOrdFromCompareMaybe : ⦃ Ord a ⦄ → OrdFromCompare (Maybe a)
  iOrdFromCompareMaybe .OrdFromCompare.compare = λ where
    Nothing  Nothing  → EQ
    Nothing  (Just _) → LT
    (Just _) Nothing  → GT
    (Just x) (Just y) → compare x y

  iOrdMaybe : ⦃ Ord a ⦄ → Ord (Maybe a)
  iOrdMaybe = record {OrdFromCompare iOrdFromCompareMaybe}

  iOrdFromCompareEither : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → OrdFromCompare (Either a b)
  iOrdFromCompareEither .OrdFromCompare.compare = λ where
    (Left  x) (Left  y) → compare x y
    (Left  _) (Right _) → LT
    (Right _) (Left  _) → GT
    (Right x) (Right y) → compare x y

  iOrdEither : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → Ord (Either a b)
  iOrdEither = record {OrdFromCompare iOrdFromCompareEither}

  iOrdFromCompareOrdering : OrdFromCompare Ordering
  iOrdFromCompareOrdering .OrdFromCompare.compare = λ where
    LT LT → EQ
    LT _  → LT
    _  LT → GT
    EQ EQ → EQ
    EQ GT → LT
    GT EQ → GT
    GT GT → EQ

  iOrdOrdering : Ord Ordering
  iOrdOrdering = record {OrdFromCompare iOrdFromCompareOrdering}
