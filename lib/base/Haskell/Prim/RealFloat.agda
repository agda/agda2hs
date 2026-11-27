{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.RealFloat where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Double
open import Haskell.Prim.Floating
open import Haskell.Prim.Int
open import Haskell.Prim.RealFrac
open import Haskell.Prim.Tuple

--------------------------------------------------
-- RealFloat

record RealFloat (a : Type) : Type₁ where
  field
    overlap ⦃ realFrac ⦄ : RealFrac a
    overlap ⦃ floating ⦄ : Floating a

    floatRadix     : a → Integer
    floatDigits    : a → Int
    floatRange     : a → Int × Int
    decodeFloat    : a → Integer × Int
    encodeFloat    : Integer → Int → a
    exponent       : a → Int
    significand    : a → a
    scaleFloat     : Int → a → a
    isNaN          : a → Bool
    isInfinite     : a → Bool
    isDenormalized : a → Bool
    isNegativeZero : a → Bool
    isIEEE         : a → Bool
    atan2          : a → a → a
open RealFloat ⦃...⦄ public hiding (realFrac; floating)

{-# COMPILE AGDA2HS RealFloat existing-class #-}

instance
  postulate iRealFloatDouble : RealFloat Double
