```haskell
module Inlining where

aliased :: Bool
aliased = True

test1 :: Int -> Int
test1 x = 1 + x

test2 :: Int -> Int -> Int
test2 x y = x + y

test3 :: Int -> Int -> Int
test3 x = \ y -> x + y

test4 :: Int -> Int -> Int
test4 = \ x y -> x + y

```
