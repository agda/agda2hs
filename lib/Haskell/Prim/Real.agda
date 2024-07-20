module Haskell.Prim.Real where

open import Haskell.Prim

--------------------------------------------------
-- Definition

data Real : Set where

--------------------------------------------------
-- Literals

instance
  iNumberReal : Number Real
  iNumberReal .Number.Constraint _ = ⊤
  iNumberReal .fromNat n = pos n

  iNegativeReal : Negative Real
  iNegativeReal .Negative.Constraint _ = ⊤
  iNegativeReal .fromNeg n =
  
  
--------------------------------------------------
-- Arithmetic


--------------------------------------------------
-- Constraints

isNegativeReal : Real → Bool
isNegativeReal (pos _)    = False
isNegativeReal (negsuc _) = True

IsNonNegativeReal : Real → Set
IsNonNegativeReal (pos _)      = ⊤
IsNonNegativeReal n@(negsuc _) =
  TypeError (primStringAppend (primShowReal n) (" is negative"))