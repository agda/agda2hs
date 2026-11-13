{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Real where

open import Haskell.Prim
open import Haskell.Prim.Double
open import Haskell.Prim.Int
open import Haskell.Prim.Num
open import Haskell.Prim.Ord
open import Haskell.Prim.Rational
open import Haskell.Prim.Word

--------------------------------------------------
-- Real

record Real (a : Type) : Type₁ where
  field
    overlap ⦃ num ⦄ : Num a
    overlap ⦃ ord ⦄ : Ord a

    toRational : a → Rational
open Real ⦃...⦄ public hiding (num; ord)

{-# COMPILE AGDA2HS Real existing-class #-}

instance
  postulate iRealNat      : Real Nat
  postulate iRealInt      : Real Int
  postulate iRealInteger  : Real Integer
  postulate iRealWord     : Real Word
  postulate iRealDouble   : Real Double
  postulate iRealRational : Real Rational
