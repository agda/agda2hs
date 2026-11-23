module DoubleNumOrd
  (doubleCases)
where

doubleCases :: Double -> Double -> Double -> [Double]
doubleCases z nz n
  = [negate z, abs nz, signum n, max z nz, min n 1.0]

