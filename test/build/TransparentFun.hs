module TransparentFun where

import Numeric.Natural (Natural)

testMyId :: Natural
testMyId = 42

testTyId :: Int -> Int
testTyId n = n

data Tree = Tip
          | Bin Tree Tree

testTreeId :: Tree -> Tree
testTreeId = id

