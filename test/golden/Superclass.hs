module Superclass where

class Super a where
  myFun :: a -> a

class (Super a) => Sub a

foo :: (Sub a) => a -> a
foo = myFun . myFun

class (Super a) => Sub2 a

class (Sub a, Sub2 a) => Subber a

bar :: (Subber a) => a -> a
bar = myFun

instance Super Int where
  myFun = (1 +)

instance Sub Int

class (Ord a) => DiscreteOrd a

instance DiscreteOrd Bool

baz :: (DiscreteOrd a) => a -> Bool
baz x = x < x

usebaz :: Bool
usebaz = baz True
