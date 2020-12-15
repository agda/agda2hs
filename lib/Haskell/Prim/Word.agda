
module Haskell.Prim.Word where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Int using (pos; negsuc)

import Agda.Builtin.Word renaming (Word64 to Word; primWord64ToNat to w2n; primWord64FromNat to n2w)
open Agda.Builtin.Word
open Agda.Builtin.Word public using (Word)

open import Haskell.Prim
open import Haskell.Prim.Integer


--------------------------------------------------
-- Literals

private
  2⁶⁴ : Nat
  2⁶⁴ = 18446744073709551616

instance
  iNumberWord : Number Word
  iNumberWord .Number.Constraint n = IsTrue (n < 2⁶⁴)
  iNumberWord .fromNat n = n2w n


--------------------------------------------------
-- Arithmetic

negateWord : Word → Word
negateWord a = n2w (2⁶⁴ - w2n a)

addWord : Word → Word → Word
addWord a b = n2w (w2n a + w2n b)

subWord : Word → Word → Word
subWord a b = addWord a (negateWord b)

mulWord : Word → Word → Word
mulWord a b = n2w (w2n a * w2n b)

eqWord : Word → Word → Bool
eqWord a b = w2n a == w2n b

ltWord : Word → Word → Bool
ltWord a b = w2n a < w2n b

showWord : Word → List Char
showWord a = primStringToList (primShowNat (w2n a))

integerToWord : Integer → Word
integerToWord (pos n)    = n2w n
integerToWord (negsuc n) = negateWord (n2w (suc n))

wordToInteger : Word → Integer
wordToInteger n = pos (w2n n)
