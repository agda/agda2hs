```haskell
module Issue324instance where

instance Eq (Bool -> Bool) where
    x == y = x True == y True && x False == y False

```
