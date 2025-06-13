module Issue210 where

import Numeric.Natural (Natural)

class Test a where
    f :: a -> a

instance Test Natural where
    f n = h
      where
        g :: Natural
        g = 3 + n
        h :: Natural
        h = n + g

f1 :: Natural -> Natural
f1 n = h1
  where
    g1 :: Natural
    g1 = 3 + n
    h1 :: Natural
    h1 = n + g1

f2 :: Natural -> Natural
f2 n = h2 n
  where
    g2 :: Natural
    g2 = 3 + n
    h2 :: Natural -> Natural
    h2 m = n + g2 + m

