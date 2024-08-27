
module Haskell.Prim.Enum where

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

@0 IfBoundedBelow : Maybe (BoundedBelow a) → (⦃ BoundedBelow a ⦄ → Set) → Set
IfBoundedBelow Nothing  k = ⊤
IfBoundedBelow (Just i) k = k ⦃ i ⦄

@0 IfBoundedAbove : Maybe (BoundedAbove a) → (⦃ BoundedAbove a ⦄ → Set) → Set
IfBoundedAbove Nothing  k = ⊤
IfBoundedAbove (Just i) k = k ⦃ i ⦄

record Enum (a : Set) : Set₁ where
  field
    BoundedBelowEnum : Maybe (BoundedBelow a)
    BoundedAboveEnum : Maybe (BoundedAbove a)
    fromEnum         : a → Int

  private
    @0 IsBoundedBelow : Set
    IsBoundedBelow = maybe ⊥ (λ _ → ⊤) BoundedBelowEnum

    @0 IsBoundedAbove : Set
    IsBoundedAbove = maybe ⊥ (λ _ → ⊤) BoundedAboveEnum

    @0 TrueIfLB : (⦃ BoundedBelow a ⦄ → Bool) → Set
    TrueIfLB C = IfBoundedBelow BoundedBelowEnum (IsTrue C)

    @0 TrueIfUB : (⦃ BoundedAbove a ⦄ → Bool) → Set
    TrueIfUB C = IfBoundedAbove BoundedAboveEnum (IsTrue C)

    @0 FalseIfLB : (⦃ BoundedBelow a ⦄ → Bool) → Set
    FalseIfLB C = IfBoundedBelow BoundedBelowEnum (IsFalse C)

    @0 FalseIfUB : (⦃ BoundedAbove a ⦄ → Bool) → Set
    FalseIfUB C = IfBoundedAbove BoundedAboveEnum (IsFalse C)

    minInt : ⦃ BoundedBelow a ⦄ → Int
    minInt ⦃ _ ⦄ = fromEnum minBound

    maxInt : ⦃ BoundedAbove a ⦄ → Int
    maxInt ⦃ _ ⦄ = fromEnum maxBound

  field
    toEnum : (n : Int) → @0 ⦃ TrueIfLB (minInt <= n) ⦄ → @0 ⦃ TrueIfUB (n <= maxInt) ⦄ → a
    succ   : (x : a) → @0 ⦃ FalseIfUB (fromEnum x == maxInt) ⦄ → a
    pred   : (x : a) → @0 ⦃ FalseIfLB (fromEnum x == minInt) ⦄ → a

    enumFrom       : @0 ⦃ IsBoundedAbove ⦄ → a → List a
    enumFromTo     : a → a → List a
    -- In the Prelude Enum instances `enumFromThenTo x x y` gives the
    -- infinite list of `x`s. The constraint is a little bit stronger than it needs to be,
    -- since it rules out different x and x₁ that maps to the same Int, but this saves us
    -- requiring an Eq instance for `a`, and it's not a terrible limitation to not be able to
    -- write [0, 2^64 .. 2^66].
    enumFromThenTo : (x x₁ : a) → @0 ⦃ IsFalse (fromEnum x == fromEnum x₁) ⦄ → a → List a
    enumFromThen   : @0 ⦃ IsBoundedBelow ⦄ → @0 ⦃ IsBoundedAbove ⦄ → (x x₁ : a) → @0 ⦃ IsFalse (fromEnum x == fromEnum x₁) ⦄ → List a

open Enum ⦃...⦄ public

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

  integerFromThenTo : (a a₁ : Integer) → @0 ⦃ IsFalse (integerToInt a == integerToInt a₁) ⦄ → Integer → List Integer
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

private
  fromTo : (from : a → Integer) (to : Integer → a)
         → a → a → List a
  fromTo from to a b = map to (enumFromTo (from a) (from b))

  fromThenTo : (from : a → Integer) (to : Integer → a)
             → (x x₁ : a) → @0 ⦃ IsFalse (fromEnum (from x) == fromEnum (from x₁)) ⦄ → a → List a
  fromThenTo from to a a₁ b = map to (enumFromThenTo (from a) (from a₁) (from b))


instance
  iEnumNat : Enum Nat
  iEnumNat .BoundedBelowEnum = Just it
  iEnumNat .BoundedAboveEnum = Nothing
  iEnumNat .fromEnum = integerToInt ∘ pos
  iEnumNat .toEnum n = unsafeIntegerToNat (intToInteger n)
  iEnumNat .succ n = suc n
  iEnumNat .pred (suc n) = n
  iEnumNat .enumFromTo = fromTo pos unsafeIntegerToNat
  iEnumNat .enumFromThenTo = fromThenTo pos unsafeIntegerToNat

  iEnumInt : Enum Int
  iEnumInt .BoundedBelowEnum      = Just it
  iEnumInt .BoundedAboveEnum      = Just it
  iEnumInt .fromEnum              = integerToInt ∘ intToInteger
  iEnumInt .toEnum         n      = integerToInt (intToInteger n)
  iEnumInt .succ           x      = integerToInt (intToInteger x + 1)
  iEnumInt .pred           x      = integerToInt (intToInteger x - 1)
  iEnumInt .enumFromTo     a b    = fromTo intToInteger integerToInt a b
  iEnumInt .enumFromThenTo a a₁ b = fromThenTo intToInteger integerToInt a a₁ b
  iEnumInt .enumFrom       a      = fromTo intToInteger integerToInt a maxBound
  iEnumInt .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo intToInteger integerToInt a a₁ maxBound
              else fromThenTo intToInteger integerToInt a a₁ minBound

  iEnumWord : Enum Word
  iEnumWord .BoundedBelowEnum      = Just it
  iEnumWord .BoundedAboveEnum      = Just it
  iEnumWord .fromEnum              = integerToInt ∘ wordToInteger
  iEnumWord .toEnum         n      = integerToWord (intToInteger n)
  iEnumWord .succ           x      = integerToWord (wordToInteger x + 1)
  iEnumWord .pred           x      = integerToWord (wordToInteger x - 1)
  iEnumWord .enumFromTo     a b    = fromTo wordToInteger integerToWord a b
  iEnumWord .enumFromThenTo a a₁ b = fromThenTo wordToInteger integerToWord a a₁ b
  iEnumWord .enumFrom       a      = fromTo wordToInteger integerToWord a maxBound
  iEnumWord .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo wordToInteger integerToWord a a₁ maxBound
              else fromThenTo wordToInteger integerToWord a a₁ minBound

private
  fromBool : Bool → Integer
  fromBool = if_then 1 else 0

  toBool : Integer → Bool
  toBool = _/= 0

instance
  iEnumBool : Enum Bool
  iEnumBool .BoundedBelowEnum      = Just it
  iEnumBool .BoundedAboveEnum      = Just it
  iEnumBool .fromEnum              = integerToInt ∘ fromBool
  iEnumBool .toEnum         n      = toBool (intToInteger n)
  iEnumBool .succ           x      = toBool (fromBool x + 1)
  iEnumBool .pred           x      = toBool (fromBool x - 1)
  iEnumBool .enumFromTo     a b    = fromTo fromBool toBool a b
  iEnumBool .enumFromThenTo a a₁ b = fromThenTo fromBool toBool a a₁ b
  iEnumBool .enumFrom       a      = fromTo fromBool toBool a maxBound
  iEnumBool .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo fromBool toBool a a₁ maxBound
              else fromThenTo fromBool toBool a a₁ minBound

private
  fromOrdering : Ordering → Integer
  fromOrdering = λ where LT → 0; EQ → 1; GT → 2

  toOrdering : Integer → Ordering
  toOrdering = λ where (pos 0) → LT; (pos 1) → EQ; _ → GT

instance
  iEnumOrdering : Enum Ordering
  iEnumOrdering .BoundedBelowEnum      = Just it
  iEnumOrdering .BoundedAboveEnum      = Just it
  iEnumOrdering .fromEnum              = integerToInt ∘ fromOrdering
  iEnumOrdering .toEnum         n      = toOrdering (intToInteger n)
  iEnumOrdering .succ           x      = toOrdering (fromOrdering x + 1)
  iEnumOrdering .pred           x      = toOrdering (fromOrdering x - 1)
  iEnumOrdering .enumFromTo     a b    = fromTo fromOrdering toOrdering a b
  iEnumOrdering .enumFromThenTo a a₁ b = fromThenTo fromOrdering toOrdering a a₁ b
  iEnumOrdering .enumFrom       a      = fromTo fromOrdering toOrdering a maxBound
  iEnumOrdering .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo fromOrdering toOrdering a a₁ maxBound
              else fromThenTo fromOrdering toOrdering a a₁ minBound

private
  fromUnit : ⊤ → Integer
  fromUnit _ = 0

  toUnit : Integer → ⊤
  toUnit _ = tt

instance
  iEnumUnit : Enum ⊤
  iEnumUnit .BoundedBelowEnum      = Just it
  iEnumUnit .BoundedAboveEnum      = Just it
  iEnumUnit .fromEnum              = integerToInt ∘ fromUnit
  iEnumUnit .toEnum         n      = toUnit (intToInteger n)
  iEnumUnit .succ           x      = toUnit (fromUnit x + 1)
  iEnumUnit .pred           x      = toUnit (fromUnit x - 1)
  iEnumUnit .enumFromTo     a b    = fromTo fromUnit toUnit a b
  iEnumUnit .enumFromThenTo a a₁ b = fromThenTo fromUnit toUnit a a₁ b
  iEnumUnit .enumFrom       a      = fromTo fromUnit toUnit a maxBound
  iEnumUnit .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo fromUnit toUnit a a₁ maxBound
              else fromThenTo fromUnit toUnit a a₁ minBound

private
  fromChar : Char → Integer
  fromChar = pos ∘ c2n

  toChar : Integer → Char
  toChar = λ where (pos n) → primNatToChar n; _ → '_'

instance
  iEnumChar : Enum Char
  iEnumChar .BoundedBelowEnum      = Just it
  iEnumChar .BoundedAboveEnum      = Just it
  iEnumChar .fromEnum              = integerToInt ∘ fromChar
  iEnumChar .toEnum         n      = toChar (intToInteger n)
  iEnumChar .succ           x      = toChar (fromChar x + 1)
  iEnumChar .pred           x      = toChar (fromChar x - 1)
  iEnumChar .enumFromTo     a b    = fromTo fromChar toChar a b
  iEnumChar .enumFromThenTo a a₁ b = fromThenTo fromChar toChar a a₁ b
  iEnumChar .enumFrom       a      = fromTo fromChar toChar a maxBound
  iEnumChar .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo fromChar toChar a a₁ maxBound
              else fromThenTo fromChar toChar a a₁ minBound

  -- Missing:
  --  Enum Double  (can't go via Integer)
