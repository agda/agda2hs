module RuntimeCast where

import Control.Exception (assert)

mySqrt :: Double -> Double
mySqrt = error "postulate: Double -> Double"

checkedSqrt :: Double -> Double
checkedSqrt
  = \ x' ->
      assert (x' >= 0)
        (assert
           (mySqrt x' >= 0 && abs (x' - mySqrt x' * mySqrt x') <= 1.0e-2)
           (mySqrt x'))

