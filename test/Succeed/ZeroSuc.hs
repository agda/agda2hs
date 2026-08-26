module ZeroSuc where

import Numeric.Natural (Natural)

test1 :: Natural
test1 = 0

test2 :: Natural -> Natural
test2 = succ

data MyNat = MyZero
           | MySuc MyNat

test3 :: MyNat -> Natural
test3 MyZero = 0
test3 (MySuc n) = succ (test3 n)

