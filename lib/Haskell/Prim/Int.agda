{-# OPTIONS --no-auto-inline #-}

-- Agda doesn't have an Int type (only Word64). With some work we
-- can represent signed ints using Word64.

module Haskell.Prim.Int where

open import Agda.Builtin.Nat
open import Agda.Builtin.Word renaming (primWord64ToNat to w2n; primWord64FromNat to n2w)
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Int using (pos; negsuc)
open import Agda.Builtin.Equality

open import Haskell.Prim
open import Haskell.Prim.Word
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool


--------------------------------------------------
-- Definition

data Int : Set where
  int64 : Word64 → Int

private
  intToWord : Int → Word64
  intToWord (int64 a) = a

  unsafeIntToNat : Int → Nat
  unsafeIntToNat a = w2n (intToWord a)


--------------------------------------------------
-- Literals

private
  2⁶⁴ : Nat
  2⁶⁴ = 18446744073709551616

  2⁶³ : Nat
  2⁶³ = 9223372036854775808

  maxInt : Nat
  maxInt = 2⁶³ - 1

instance
  iNumberInt : Number Int
  iNumberInt .Number.Constraint n = IsTrue (n < 2⁶³)
  iNumberInt .fromNat n = int64 (n2w n)

  iNegativeInt : Negative Int
  iNegativeInt .Negative.Constraint n = IsTrue (n < 1 + 2⁶³)
  iNegativeInt .fromNeg n = int64 (n2w (2⁶⁴ - n))


--------------------------------------------------
-- Arithmetic

isNegativeInt : Int → Bool
isNegativeInt (int64 w) = maxInt < w2n w

eqInt : Int → Int → Bool
eqInt (int64 a) (int64 b) = w2n a == w2n b

negateInt : Int → Int
negateInt (int64 a) = int64 (n2w (2⁶⁴ - w2n a))

intToInteger : Int → Integer
intToInteger a = if isNegativeInt a then negsuc (unsafeIntToNat (negateInt a) - 1)
                                    else pos (unsafeIntToNat a)

integerToInt : Integer → Int
integerToInt (pos    n) = int64 (n2w n)
integerToInt (negsuc n) = negateInt (int64 (n2w (suc n)))

private
  ltPosInt : Int → Int → Bool
  ltPosInt (int64 a) (int64 b) = ltWord a b

ltInt : Int → Int → Bool
ltInt a b with isNegativeInt a | isNegativeInt b
... | true  | false = true
... | false | true  = false
... | true  | true  = ltPosInt (negateInt b) (negateInt a)
... | false | false = ltPosInt a b

addInt : Int → Int → Int
addInt (int64 a) (int64 b) = int64 (addWord a b)

subInt : Int → Int → Int
subInt a b = addInt a (negateInt b)

mulInt : Int → Int → Int
mulInt (int64 a) (int64 b) = int64 (mulWord a b)

absInt : Int → Int
absInt a = if isNegativeInt a then negateInt a else a

signInt : Int → Int
signInt a = if      isNegativeInt a then -1
            else if eqInt a 0       then 0 else 1

showInt : Int → List Char
showInt a = showInteger (intToInteger a)


--------------------------------------------------
-- Constraints

IsNonNegativeInt : Int → Set
IsNonNegativeInt a@(int64 _) =
  if isNegativeInt a then TypeError (primStringAppend (primStringFromList (showInt a)) " is negative")
                     else ⊤

intToNat : (a : Int) → ⦃ IsNonNegativeInt a ⦄ → Nat
intToNat a = unsafeIntToNat a
