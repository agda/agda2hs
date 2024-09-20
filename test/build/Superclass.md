```haskell
module Superclass where

class Super a where
    myFun :: a -> a

class Super a => Sub a where

foo :: Sub a => a -> a
foo = myFun . myFun

class Super a => Sub2 a where

class (Sub a, Sub2 a) => Subber a where

bar :: Subber a => a -> a
bar = myFun . id

instance Super Int where
    myFun = (1 +)

instance Sub Int where

class Ord a => DiscreteOrd a where

instance DiscreteOrd Bool where

baz :: DiscreteOrd a => a -> Bool
baz x = x < x

usebaz :: Bool
usebaz = baz True

```
