module CompileToInstanceUnboxedDefer
  (test)
where

import Numeric.Natural (Natural)

test :: Bool
test = x == y
  where
    x :: Natural
    x = 3
    y :: Natural
    y = 4

