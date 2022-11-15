module NatLitPat where

import Numeric.Natural (Natural)

fac :: Natural -> Natural
fac 0 = 1
fac n = n * fac (n - 1)

fib :: Natural -> Natural
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

