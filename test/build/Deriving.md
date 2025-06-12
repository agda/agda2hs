```haskell
{-# LANGUAGE StandaloneDeriving, DerivingStrategies,
  DeriveAnyClass, GeneralizedNewtypeDeriving #-}
module Deriving where

data Planet = Mercury
            | Venus
            | Earth
            | Mars
            | Jupiter
            | Saturn
            | Uranus
            | Neptune
            | Pluto
                deriving (Read)

deriving instance Eq Planet

deriving instance Ord Planet

deriving stock instance Show Planet

class Clazz a where
    foo :: a -> Int
    bar :: a -> Bool

deriving anyclass instance Clazz Planet

data Optional a = Of a
                | Empty

deriving instance (Eq a) => Eq (Optional a)

newtype Duo a b = MkDuo (a, b)

deriving newtype instance (Eq a, Eq b) => Eq (Duo a b)

```
