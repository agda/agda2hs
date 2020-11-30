
module Haskell.Prim.Word where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit
open import Agda.Builtin.Int using (pos; negsuc)

import Agda.Builtin.Word renaming (primWord64ToNat to w2n; primWord64FromNat to n2w)
open Agda.Builtin.Word
open Agda.Builtin.Word public using (Word64)

open import Haskell.Prim
open import Haskell.Prim.Integer


--------------------------------------------------
-- Literals

private
  2⁶⁴ : Nat
  2⁶⁴ = 18446744073709551616

instance
  iNumberWord : Number Word64
  iNumberWord .Number.Constraint n = IsTrue (n < 2⁶⁴)
  iNumberWord .fromNat n = n2w n


--------------------------------------------------
-- Arithmetic

negateWord : Word64 → Word64
negateWord a = n2w (2⁶⁴ - w2n a)

addWord : Word64 → Word64 → Word64
addWord a b = n2w (w2n a + w2n b)

subWord : Word64 → Word64 → Word64
subWord a b = addWord a (negateWord b)

mulWord : Word64 → Word64 → Word64
mulWord a b = n2w (w2n a * w2n b)

eqWord : Word64 → Word64 → Bool
eqWord a b = w2n a == w2n b

ltWord : Word64 → Word64 → Bool
ltWord a b = w2n a < w2n b

showWord : Word64 → List Char
showWord a = primStringToList (primShowNat (w2n a))

integerToWord : Integer → Word64
integerToWord (pos n)    = n2w n
integerToWord (negsuc n) = negateWord (n2w (suc n))
