module Numbers where

import Numeric.Natural (Natural)

posNatural :: Natural
posNatural = 14

posInteger :: Integer
posInteger = 52

negInteger :: Integer
negInteger = -1001

natToPos :: Natural -> Integer
natToPos n = fromIntegral n

natToNeg :: Natural -> Integer
natToNeg n = (negate . fromIntegral) n

