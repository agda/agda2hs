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