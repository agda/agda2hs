module File2
  (bar, num', first)
where

import File1 (foo)
import Numeric.Natural (Natural)

bar :: [a]
bar = foo

num' :: Natural
num' = 42

first :: [a] -> a
first (x : _) = x

