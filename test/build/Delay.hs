module Delay where

collatz :: Int -> Int
collatz x
  = if x == 0 then 0 else
      if even x then collatz (div x 2) else collatz (3 * x + 1)

