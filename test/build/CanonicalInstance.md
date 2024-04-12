```haskell
module CanonicalInstance where

class ClassA a where
    myA :: a

class ClassA b => ClassB b where

myB :: ClassB b => b
myB = myA

```
