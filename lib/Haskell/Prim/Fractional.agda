{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Fractional where

open import Haskell.Prim
open import Haskell.Floating
open import Haskell.Prim.RealFrac

--------------------------------------------------
-- Fractional

record Fractional (a : Set) : Set where
  infixl 7 _/_
  field
    _/_ : a → a → a
    recip : a → a
    fromRational : Rational → a
open Fractional ⦃... ⦄  public

{-# COMPILE AGDA2HS Fractional existing-class #-}

