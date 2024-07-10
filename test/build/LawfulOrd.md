```haskell
module LawfulOrd where

data Ordered a = Gt a a
               | Lt a a
               | E a a

order :: Ord a => a -> a -> Ordered a
order left right
  = if left < right then Lt left right else
      if left == right then E left right else Gt left right

```
