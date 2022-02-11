
module Haskell.Prim.Word where

open import Haskell.Prim
open import Haskell.Prim.Integer

import Agda.Builtin.Word renaming (Word64 to Word)
open Agda.Builtin.Word public using (Word)


--------------------------------------------------
-- Literals

private
  2⁶⁴ : Natural
  2⁶⁴ = 18446744073709551616

instance
  iNumberWord : Number Word
  iNumberWord .Number.Constraint n = IsTrue (ltNat n 2⁶⁴)
  iNumberWord .fromNat n = n2w n


--------------------------------------------------
-- Arithmetic

negateWord : Word → Word
negateWord a = n2w (monusNat 2⁶⁴ (w2n a))

addWord : Word → Word → Word
addWord a b = n2w (addNat (w2n a) (w2n b))

subWord : Word → Word → Word
subWord a b = addWord a (negateWord b)

mulWord : Word → Word → Word
mulWord a b = n2w (mulNat (w2n a) (w2n b))

eqWord : Word → Word → Bool
eqWord a b = eqNat (w2n a) (w2n b)

ltWord : Word → Word → Bool
ltWord a b = ltNat (w2n a) (w2n b)

showWord : Word → List Char
showWord a = primStringToList (primShowNat (w2n a))

integerToWord : Integer → Word
integerToWord (pos n)    = n2w n
integerToWord (negsuc n) = negateWord (n2w (suc n))

wordToInteger : Word → Integer
wordToInteger n = pos (w2n n)
