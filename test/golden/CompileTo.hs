module CompileTo where

import Numeric.Natural (Natural)

test1 :: [Int]
test1 = [1, 2, 3]

test2 :: [Int]
test2 = map (+ 1) [1, 2, 3]

llength :: [a] -> Natural
llength [] = 0
llength (x : xs) = 1 + llength xs

test3 :: Natural
test3 = llength test1

