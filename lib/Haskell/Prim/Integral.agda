module Haskell.Prim.Integral where

open import Haskell.Prim

--------------------------------------------------
-- Definition

data Integral : Set where

--------------------------------------------------
-- Literals

instance
  iNumberIntegral : Number Integral
  iNumberIntegral .Number.Constraint _ = ⊤
  iNumberIntegral .fromNat n = pos n

  iNegativeIntegral : Negative Integral
  iNegativeIntegral .Negative.Constraint _ = ⊤
  iNegativeIntegral .fromNeg n =
  
  
--------------------------------------------------
-- Arithmetic

