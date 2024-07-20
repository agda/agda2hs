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

--------------------------------------------------
-- Constraints

isNegativeIntegral : Integral → Bool
isNegativeIntegral (pos _)    = False
isNegativeIntegral (negsuc _) = True

IsNonNegativeIntegral : Integral → Set
IsNonNegativeIntegral (pos _)      = ⊤
IsNonNegativeIntegral n@(negsuc _) =
  TypeError (primStringAppend (primShowIntegral n) (" is negative"))