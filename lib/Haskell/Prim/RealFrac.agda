module Haskell.Prim.RealFrac where

open import Haskell.Prim

--------------------------------------------------
-- Literals

instance
  iNumberRealFrac : Number RealFrac
  iNumberRealFrac .Number.Constraint _ = ⊤
  iNumberRealFrac .fromNat n = pos n

  iNegativeRealFrac : Negative RealFrac
  iNegativeRealFrac .Negative.Constraint _ = ⊤
  iNegativeRealFrac .fromNeg n = negNat n

postulate
  properFraction : RealFrac → -- todo (Int, Realfrac)
  truncate       : RealFrac → Int
  round          : RealFrac → Int
  ceiling        : RealFrac → Int
  floor          : RealFrac → Int

--------------------------------------------------
-- Arithmetic


--------------------------------------------------
-- Constraints

isNegativeRealFrac : RealFrac → Bool
isNegativeRealFrac (pos _)    = False
isNegativeRealFrac (negsuc _) = True

IsNonNegativeRealFrac : Real → Set
IsNonNegativeRealFrac (pos _)      = ⊤
IsNonNegativeRealFrac n@(negsuc _) =
  TypeError (primStringAppend (primShowRealFrac n) (" is negative"))