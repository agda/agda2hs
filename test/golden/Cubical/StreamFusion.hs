module Cubical.StreamFusion where

data Stream a = (:>){shead :: a, stail :: Stream a}

smap :: (a -> b) -> Stream a -> Stream b
smap f (x :> xs) = f x :> smap f xs

