{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Rational where

open import Haskell.Prim
open import Haskell.Prim.Integer

--------------------------------------------------
-- Definition
  
record Ratio (a : Set) : Set where
  inductive
  constructor _:%_
  field
    numerator : a
    denominator : a
open Ratio ⦃...⦄ public

-- Rational numbers, represented as a ratio of two 'Integer' values.
-- A rational number may be constructed using the '%' operator.
Rational : Set
Rational = Ratio Integer

