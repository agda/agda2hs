module Issue65
  (yeet, xx)
where

yeet :: Bool -> a -> a -> a
yeet False x y = y
yeet True x y = x

xx :: Int
xx = yeet True 1 2

