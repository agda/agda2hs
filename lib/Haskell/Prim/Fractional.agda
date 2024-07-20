module Haskell.Prim.Fractional where

open import Haskell.Prim

--------------------------------------------------
-- Definition

data Fractional : Set where

--------------------------------------------------
-- Literals

instance
  iNumberFractional : Number Fractional
  iNumberFractional .Number.Constraint _ = ⊤
  iNumberFractional .fromNat n = pos n

  iNegativeFractional : Negative Fractional
  iNegativeFractional .Negative.Constraint _ = ⊤
  iNegativeFractional .fromNeg n = 
  
--------------------------------------------------
-- Arithmetic



--------------------------------------------------
-- Constraints

isNegativeFractional : Fractional → Bool
isNegativeFractional (pos _)    = False
isNegativeFractional (negsuc _) = True

IsNonNegativeFractional : Fractional → Set
IsNonNegativeFractional (pos _)      = ⊤
IsNonNegativeFractional n@(negsuc _) =
  TypeError (primStringAppend (primShowFractional n) (" is negative"))