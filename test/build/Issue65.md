```haskell
module Issue65 where

yeet :: Bool -> a -> a -> a
yeet False x y = y
yeet True x y = x

xx :: Int
xx = yeet True 1 2

```
