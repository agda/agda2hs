{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Fractional where

open import Haskell.Prim
open import Haskell.Prim.Double
open import Haskell.Prim.Num
open import Haskell.Prim.Rational

--------------------------------------------------
-- Fractional

record Fractional (a : Type) : Type₁ where
  field
    overlap ⦃ num ⦄ : Num a

    _/_          : a → a → a
    recip        : a → a
    fromRational : Rational → a
open Fractional ⦃...⦄ public hiding (num)

{-# COMPILE AGDA2HS Fractional existing-class #-}

instance
  postulate iFractionalDouble   : Fractional Double
  postulate iFractionalRational : Fractional Rational
