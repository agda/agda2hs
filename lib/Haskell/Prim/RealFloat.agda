module Haskell.Prim.RealFloat where

open import Haskell.Prim
open import Haskell.Prim.Int
open import Haskell.Prim.Bool

-- The RealFloat typeclass functions
postulate
  floatRadix       : RealFloat → Int
  floatDigits      : RealFloat → Int
  floatRange       : RealFloat → Σ Int (λ _ → Int)
  decodeFloat      : RealFloat → Σ Int (λ _ → Int)
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

