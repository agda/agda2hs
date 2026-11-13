
module Haskell.Prim.Rational where

open import Haskell.Prim

--------------------------------------------------
-- Ratio

-- | Rational numbers, with numerator and denominator of some 'Integral' type.
-- The constructor is compiled to Haskell's @%@ from @Data.Ratio@, since
-- @Data.Ratio@ does not export the @:%@ constructor.
record Ratio (a : Type) : Type where
  constructor _:%_
  field
    numerator : a
    denominator : a
open Ratio public

-- | Arbitrary-precision rational numbers, represented as a ratio of two
-- 'Integer' values.
Rational : Type
Rational = Ratio Integer
