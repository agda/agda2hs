module Inlining
  (aliased, test1, test2)
where

aliased :: Bool
aliased = True

test1 :: Int -> Int
test1 x = 1 + x

test2 :: Int -> Int -> Int
test2 x y = x + y

