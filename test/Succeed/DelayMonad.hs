module DelayMonad
  (pureDelay, mapDelay, bindDelay')
where

import Numeric.Natural (Natural)

pureDelay :: Natural
pureDelay = 1

mapDelay :: Natural -> Natural
mapDelay = (+ 1)

bindDelay' :: Natural -> Natural
bindDelay' m = let x = m in seq x (x + 1)

