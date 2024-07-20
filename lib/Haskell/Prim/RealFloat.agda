module Haskell.Prim.RealFloat where

open import Haskell.Prim
open import Haskell.Prim.Int
open import Haskell.Prim.Bool

--------------------------------------------------
-- Literals

instance
  iNumberRealFloat : Number RealFloat
  iNumberRealFloat .Number.Constraint _ = ⊤
  iNumberRealFloat .fromNat n = pos n

  iNegativeRealFloat : Negative RealFloat
  iNegativeRealFloat .Negative.Constraint _ = ⊤
  iNegativeRealFloat .fromNeg n = negNat n

-- The RealFloat typeclass functions
postulate
  floatRadix       : RealFloat → Int
  floatDigits      : RealFloat → Int
  floatRange       : RealFloat → -- todo (Int, Int)
  decodeFloat      : RealFloat → -- todo (Int, Int)
  encodeFloat      : Int → Int → RealFloat
  exponent         : RealFloat → Int
  significand      : RealFloat → Float
  scaleFloat       : Int → RealFloat → RealFloat
  isNaN            : RealFloat → Bool
  isInfinite       : RealFloat → Bool
  isDenormalized   : RealFloat → Bool
  isNegativeZero   : RealFloat → Bool
  isIEEE           : RealFloat → Bool
  atan2			   : RealFloat → RealFloat → RealFloat
  
--------------------------------------------------
-- Arithmetic


--------------------------------------------------
-- Constraints

isNegativeRealFloat : RealFloat → Bool
isNegativeRealFloat (pos _)    = False
isNegativeRealFloat (negsuc _) = True

IsNonNegativeRealFloat : RealFloat → Set
IsNonNegativeRealFloat (pos _)      = ⊤
IsNonNegativeRealFloat n@(negsuc _) =
  TypeError (primStringAppend (primShowRealFloat n) (" is negative"))