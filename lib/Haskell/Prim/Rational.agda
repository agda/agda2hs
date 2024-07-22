{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Rational where

open import Haskell.Prim.Integer

--------------------------------------------------
-- Definition

-- | Rational numbers, with numerator and denominator of some 'Integral' type.
data Ratio (a : Set) : Set where
  :% : a → a → Ratio a
  numerator : Ratio a → a
  denominator : Ratio a → a

-- | Arbitrary-precision rational numbers, represented as a ratio of
-- two 'Integer' values.  A rational number may be constructed using
-- the '%' operator.
Rational : Set
Rational = Ratio Integer

