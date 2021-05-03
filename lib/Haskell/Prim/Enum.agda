
module Haskell.Prim.Enum where

open import Agda.Builtin.Nat as Nat hiding (_==_; _<_; _+_; _*_; _-_)
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Int using (pos; negsuc)

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Bounded
open import Haskell.Prim.Either
open import Haskell.Prim.Eq
open import Haskell.Prim.Functor
open import Haskell.Prim.Int
open import Haskell.Prim.Integer
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Num
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple
open import Haskell.Prim.Word


--------------------------------------------------
-- Enum
--    Assumptions: unbounded enums have no constraints on their
--    operations and bounded enums should work on all values between
--    minBound and maxBound. Unbounded enums do not support enumFrom
--    and enumFromThen (since they return infinite lists).

IfBoundedBelow : Maybe (BoundedBelow a) → (⦃ BoundedBelow a ⦄ → Set) → Set
IfBoundedBelow Nothing  k = ⊤
IfBoundedBelow (Just i) k = k ⦃ i ⦄

IfBoundedAbove : Maybe (BoundedAbove a) → (⦃ BoundedAbove a ⦄ → Set) → Set
IfBoundedAbove Nothing  k = ⊤
IfBoundedAbove (Just i) k = k ⦃ i ⦄

record Enum (a : Set) : Set₁ where
  field
    BoundedBelowEnum : Maybe (BoundedBelow a)
    BoundedAboveEnum : Maybe (BoundedAbove a)
    fromEnum         : a → Int

  private
    IsBoundedBelow : Set
    IsBoundedBelow = maybe ⊥ (λ _ → ⊤) BoundedBelowEnum

    IsBoundedAbove : Set
    IsBoundedAbove = maybe ⊥ (λ _ → ⊤) BoundedAboveEnum

    TrueIfLB : (⦃ BoundedBelow a ⦄ → Bool) → Set
    TrueIfLB C = IfBoundedBelow BoundedBelowEnum (IsTrue C)

    TrueIfUB : (⦃ BoundedAbove a ⦄ → Bool) → Set
    TrueIfUB C = IfBoundedAbove BoundedAboveEnum (IsTrue C)

    FalseIfLB : (⦃ BoundedBelow a ⦄ → Bool) → Set
    FalseIfLB C = IfBoundedBelow BoundedBelowEnum (IsFalse C)

    FalseIfUB : (⦃ BoundedAbove a ⦄ → Bool) → Set
    FalseIfUB C = IfBoundedAbove BoundedAboveEnum (IsFalse C)

    minInt : ⦃ BoundedBelow a ⦄ → Int
    minInt ⦃ _ ⦄ = fromEnum minBound

    maxInt : ⦃ BoundedAbove a ⦄ → Int
    maxInt ⦃ _ ⦄ = fromEnum maxBound

  field
    toEnum : (n : Int) → ⦃ TrueIfLB (minInt <= n) ⦄ → ⦃ TrueIfUB (n <= maxInt) ⦄ → a
    succ   : (x : a) → ⦃ FalseIfUB (fromEnum x == maxInt) ⦄ → a
    pred   : (x : a) → ⦃ FalseIfLB (fromEnum x == minInt) ⦄ → a

    enumFrom       : ⦃ IsBoundedAbove ⦄ → a → List a
    enumFromTo     : a → a → List a
    -- In the Prelude Enum instances `enumFromThenTo x x y` gives the
    -- infinite list of `x`s. The constraint is a little bit stronger than it needs to be,
    -- since it rules out different x and x₁ that maps to the same Int, but this saves us
    -- requiring an Eq instance for `a`, and it's not a terrible limitation to not be able to
    -- write [0, 2^64 .. 2^66].
    enumFromThenTo : (x x₁ : a) → ⦃ IsFalse (fromEnum x == fromEnum x₁) ⦄ → a → List a
    enumFromThen   : ⦃ IsBoundedBelow ⦄ → ⦃ IsBoundedAbove ⦄ → (x x₁ : a) → ⦃ IsFalse (fromEnum x == fromEnum x₁) ⦄ → List a

open Enum ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Enum existing-class #-}

private
  divNat : Nat → Nat → Nat
  divNat a 0       = 0
  divNat a (suc b) = div-helper 0 b a b

  diff : Integer → Integer → Maybe Nat
  diff a b =
    case a - b of λ where
      (pos n)    → Just n
      (negsuc _) → Nothing

  unsafeIntegerToNat : Integer → Nat
  unsafeIntegerToNat (pos n) = n
  unsafeIntegerToNat (negsuc _) = 0

  integerFromCount : Integer → Integer → Nat → List Integer
  integerFromCount a step 0       = []
  integerFromCount a step (suc n) = a ∷ integerFromCount (a + step) step n

  integerFromTo : Integer → Integer → List Integer
  integerFromTo a b = maybe [] (integerFromCount a 1 ∘ suc) (diff b a)

  integerFromThenTo : (a a₁ : Integer) → ⦃ IsFalse (integerToInt a == integerToInt a₁) ⦄ → Integer → List Integer
  integerFromThenTo a a₁ b =
    case compare a a₁ of λ where
      LT → maybe [] (λ d → integerFromCount a (a₁ - a) (suc (divNat d (unsafeIntegerToNat (a₁ - a))))) (diff b a)
      EQ → [] -- impossible
      GT → maybe [] (λ d → integerFromCount a (a₁ - a) (suc (divNat d (unsafeIntegerToNat (a - a₁))))) (diff a b)

instance
  iEnumInteger : Enum Integer
  iEnumInteger .BoundedBelowEnum  = Nothing
  iEnumInteger .BoundedAboveEnum  = Nothing
  iEnumInteger .fromEnum          = integerToInt
  iEnumInteger .toEnum          n = intToInteger n
  iEnumInteger .succ              = _+ 1
  iEnumInteger .pred              = _- 1
  iEnumInteger .enumFromTo        = integerFromTo
  iEnumInteger .enumFromThenTo    = integerFromThenTo

module _ (from : a → Integer) (to : Integer → a) where
  private
    fromTo : a → a → List a
    fromTo a b = map to (enumFromTo (from a) (from b))

    fromThenTo : (x x₁ : a) → ⦃ IsFalse (fromEnum (from x) == fromEnum (from x₁)) ⦄ → a → List a
    fromThenTo a a₁ b = map to (enumFromThenTo (from a) (from a₁) (from b))

  unboundedEnumViaInteger : Enum a
  unboundedEnumViaInteger .BoundedBelowEnum      = Nothing
  unboundedEnumViaInteger .BoundedAboveEnum      = Nothing
  unboundedEnumViaInteger .fromEnum              = integerToInt ∘ from
  unboundedEnumViaInteger .toEnum         n      = to (intToInteger n)
  unboundedEnumViaInteger .succ           x      = to (from x + 1)
  unboundedEnumViaInteger .pred           x      = to (from x - 1)
  unboundedEnumViaInteger .enumFromTo     a b    = fromTo a b
  unboundedEnumViaInteger .enumFromThenTo a a₁ b = fromThenTo a a₁ b

  boundedBelowEnumViaInteger : ⦃ Ord a ⦄ → ⦃ BoundedBelow a ⦄ → Enum a
  boundedBelowEnumViaInteger .BoundedBelowEnum      = Just it
  boundedBelowEnumViaInteger .BoundedAboveEnum      = Nothing
  boundedBelowEnumViaInteger .fromEnum              = integerToInt ∘ from
  boundedBelowEnumViaInteger .toEnum         n      = to (intToInteger n)
  boundedBelowEnumViaInteger .succ           x      = to (from x + 1)
  boundedBelowEnumViaInteger .pred           x      = to (from x - 1)
  boundedBelowEnumViaInteger .enumFromTo     a b    = fromTo a b
  boundedBelowEnumViaInteger .enumFromThenTo a a₁ b = fromThenTo a a₁ b

  boundedAboveEnumViaInteger : ⦃ Ord a ⦄ → ⦃ BoundedAbove a ⦄ → Enum a
  boundedAboveEnumViaInteger .BoundedBelowEnum      = Nothing
  boundedAboveEnumViaInteger .BoundedAboveEnum      = Just it
  boundedAboveEnumViaInteger .fromEnum              = integerToInt ∘ from
  boundedAboveEnumViaInteger .toEnum         n      = to (intToInteger n)
  boundedAboveEnumViaInteger .succ           x      = to (from x + 1)
  boundedAboveEnumViaInteger .pred           x      = to (from x - 1)
  boundedAboveEnumViaInteger .enumFrom       a      = fromTo a maxBound
  boundedAboveEnumViaInteger .enumFromTo     a b    = fromTo a b
  boundedAboveEnumViaInteger .enumFromThenTo a a₁ b = fromThenTo a a₁ b

  boundedEnumViaInteger : ⦃ Ord a ⦄ → ⦃ Bounded a ⦄ → Enum a
  boundedEnumViaInteger .BoundedBelowEnum      = Just it
  boundedEnumViaInteger .BoundedAboveEnum      = Just it
  boundedEnumViaInteger .fromEnum              = integerToInt ∘ from
  boundedEnumViaInteger .toEnum         n      = to (intToInteger n)
  boundedEnumViaInteger .succ           x      = to (from x + 1)
  boundedEnumViaInteger .pred           x      = to (from x - 1)
  boundedEnumViaInteger .enumFromTo     a b    = fromTo a b
  boundedEnumViaInteger .enumFromThenTo a a₁ b = fromThenTo a a₁ b
  boundedEnumViaInteger .enumFrom       a      = fromTo a maxBound
  boundedEnumViaInteger .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo a a₁ maxBound
              else fromThenTo a a₁ minBound

instance
  iEnumNatural : Enum Nat
  iEnumNatural = boundedBelowEnumViaInteger pos unsafeIntegerToNat

  iEnumInt : Enum Int
  iEnumInt = boundedEnumViaInteger intToInteger integerToInt

  iEnumWord : Enum Word
  iEnumWord = boundedEnumViaInteger wordToInteger integerToWord

  iEnumBool : Enum Bool
  iEnumBool = boundedEnumViaInteger (if_then 1 else 0) (_/= 0)

  iEnumOrdering : Enum Ordering
  iEnumOrdering = boundedEnumViaInteger (λ where LT → 0; EQ → 1; GT → 2)
                                        (λ where (pos 0) → LT; (pos 1) → EQ; _ → GT)

  iEnumUnit : Enum (Tuple [])
  iEnumUnit = boundedEnumViaInteger (λ _ → 0) (λ _ → [])

  iEnumChar : Enum Char
  iEnumChar = boundedEnumViaInteger (pos ∘ primCharToNat)
                                    λ where (pos n) → primNatToChar n; _ → '_'

  -- Missing:
  --  Enum Double  (can't go via Integer)
