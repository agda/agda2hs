module Haskell.Extra.Erase where

rezzCong :: (a -> b) -> a -> b
rezzCong f x = f x

rezzCong2 :: (a -> b -> c) -> a -> b -> c
rezzCong2 f x y = f x y

rezzHead :: [a] -> a
rezzHead (x : xs) = x

rezzTail :: [a] -> [a]
rezzTail (x : xs) = xs

rezzErase :: ()
rezzErase = ()

