module Haskell.Prim.RealFrac where

open import Haskell.Prim
open import Haskell.Prim.Int
open import Haskell.Prim.Integral
open import Haskell.Prim.Tuple

--------------------------------------------------
-- RealFrac

record RealFrac (a : Set) : Set where
  field
    properFraction : a → (Int × a)
    truncate       : a → Integral
    round          : a → Integral
    ceiling        : a → Integral
    floor          : a → Integral
open RealFrac ⦃... ⦄  public

{-# COMPILE AGDA2HS RealFrac existing-class #-}

