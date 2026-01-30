{-# LANGUAGE TypeOperators #-}
module EqualityExample where

coerce' :: a ~ b => a -> b
coerce' x = x

sameList :: x ~ y => x -> y -> [x]
sameList vx vy = [vx, coerce' vy]

