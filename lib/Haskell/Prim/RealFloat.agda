module Haskell.Prim.RealFloat where

open import Haskell.Prim
open import Haskell.Prim.Int
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool

--------------------------------------------------
-- RealFloat

record RealFloat (a : Set) : Set where
  field
	floatRadix       : a → Integer
	floatDigits      : a → Int
	floatRange       : a → (Int × Int)
	decodeFloat      : a → (Integer × Int)
	encodeFloat      : Integer → Int → a
	exponent         : a → Int
	significand      : a → a
	scaleFloat       : Int → a → a
	isNaN            : a → Bool
	isInfinite       : a → Bool
	isDenormalized   : a → Bool
	isNegativeZero   : a → Bool
	isIEEE           : a → Bool
	atan2			 : a → a → a
open RealFloat ⦃... ⦄  public

{-# COMPILE AGDA2HS RealFloat existing-class #-}

