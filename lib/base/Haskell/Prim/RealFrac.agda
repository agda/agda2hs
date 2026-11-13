{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.RealFrac where

open import Haskell.Prim
open import Haskell.Prim.Double
open import Haskell.Prim.Fractional
open import Haskell.Prim.Integral
open import Haskell.Prim.Rational
open import Haskell.Prim.Real
open import Haskell.Prim.Tuple

--------------------------------------------------
-- RealFrac

record RealFrac (a : Type) : Type₁ where
  field
    overlap ⦃ real ⦄ : Real a
    overlap ⦃ fractional ⦄ : Fractional a

    properFraction               : ⦃ Integral b ⦄ → a → b × a
    truncate round ceiling floor : ⦃ Integral b ⦄ → a → b
open RealFrac ⦃...⦄ public hiding (real; fractional)

{-# COMPILE AGDA2HS RealFrac existing-class #-}

instance
  postulate iRealFracDouble   : RealFrac Double
  postulate iRealFracRational : RealFrac Rational
