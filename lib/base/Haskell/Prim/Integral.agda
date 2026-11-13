{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Integral where

open import Haskell.Prim
open import Haskell.Prim.Enum
open import Haskell.Prim.Int
open import Haskell.Prim.Real
open import Haskell.Prim.Tuple
open import Haskell.Prim.Word

--------------------------------------------------
-- Integral

record Integral (a : Type) : Type₁ where
  field
    overlap ⦃ real ⦄ : Real a
    overlap ⦃ enum ⦄ : Enum a

    quot rem div mod : a → a → a
    quotRem divMod   : a → a → a × a
    toInteger        : a → Integer
open Integral ⦃...⦄ public hiding (real; enum)

{-# COMPILE AGDA2HS Integral existing-class #-}

instance
  postulate iIntegralNat     : Integral Nat
  postulate iIntegralInt     : Integral Int
  postulate iIntegralInteger : Integral Integer
  postulate iIntegralWord    : Integral Word
