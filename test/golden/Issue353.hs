module Issue353 where

hello :: Bool -> Bool
hello a = a

world :: Bool -> Bool
world a = hello a

world2 :: Bool -> Bool
world2 a = hello a

foo :: Bool -> Int -> Bool
foo a b = not a

bar :: Bool -> Bool
bar b = foo True 0

