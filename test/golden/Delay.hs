module Delay where

collatz :: Int -> Int
collatz x
  | x == 0 = 0
  | even x = collatz (div x 2)
  | otherwise = collatz (3 * x + 1)
