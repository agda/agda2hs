```haskell
module Vector where

data Vec a = Nil
           | Cons a (Vec a)

mapV :: (a -> b) -> Vec a -> Vec b
mapV f Nil = Nil
mapV f (Cons x xs) = Cons (f x) (mapV f xs)

tailV :: Vec a -> Vec a
tailV (Cons x xs) = xs

```
