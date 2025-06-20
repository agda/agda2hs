```haskell
module Issue308 where

class Class a where
    foo :: a -> a

instance Class Int where
    foo = (+ 1)

tester :: Int
tester = foo 41

```
