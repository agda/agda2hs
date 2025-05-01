```haskell
module TypeDirected where

myconst :: a -> a -> a
myconst x y = x

fn :: Bool -> Int
fn False = 0
fn True = 5

test1 :: Int
test1 = fn True

test2 :: Int
test2 = fn False

```
