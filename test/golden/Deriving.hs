{-# LANGUAGE StandaloneDeriving #-}
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

deriving instance Eq Planet

data Optional a = Of a
                | Empty

deriving instance (Eq a) => Eq (Optional a)

