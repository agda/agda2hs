module Haskell.Data.Char where

open import Agda.Builtin.Char
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Int using (pos)
open import Haskell.Prim.Int
open import Haskell.Prim using (_∘_; eqNat)

-- Translating builtin, postulated Agda functions
-- to Haskell functions in Data.Char.

isLower isDigit isAlpha isSpace isAscii
  isLatin1 isPrint isHexDigit : Char → Bool
isLower = primIsLower
isDigit = primIsDigit
isAlpha = primIsAlpha
isSpace = primIsSpace
isAscii = primIsAscii
isLatin1 = primIsLatin1
isPrint = primIsPrint
isHexDigit = primIsHexDigit
toUpper toLower : Char → Char
toUpper = primToUpper
toLower = primToLower
ord : Char → Int
ord = (integerToInt ∘ pos) ∘ primCharToNat
chr : Int → Char
chr = primNatToChar ∘ unsafeIntToNat
