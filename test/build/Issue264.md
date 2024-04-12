```haskell
module Issue264 where

data Term = Dummy

reduce :: Term -> Term
reduce v = go v
  where
    go :: Term -> Term
    go v = v

```
