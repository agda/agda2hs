```haskell
module Default where

class HasDefault a where
    theDefault :: a

instance HasDefault Bool where
    theDefault = False

test :: Bool
test = theDefault

```
