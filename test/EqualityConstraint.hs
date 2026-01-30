{-# LANGUAGE TypeOperators #-}
module EqualityConstraint where

c :: *
c = error "postulate: *"

myFunc :: a ~ b => c
myFunc = error "postulate:   a ~ b => c"

