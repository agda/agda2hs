module Delay where

div' :: Int -> Int -> Int
div' = error "postulate: Int -> Int -> Int"

mod' :: Int -> Int -> Int
mod' = error "postulate: Int -> Int -> Int"

even' :: Int -> Bool
even' x = mod' x 2 == 0

collatz :: Int -> Int
collatz x
  = if x == 0 then 0 else
      if even' x then collatz (div' x 2) else collatz (3 * x + 1)

