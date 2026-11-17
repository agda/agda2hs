module CompileToFunctionTarget
  (target)
where

import Numeric.Natural (Natural)

target :: [Natural] -> Natural
target xs = go xs
  where
    go :: [Natural] -> Natural
    go [] = 0
    go (x : xs) = x + go xs

