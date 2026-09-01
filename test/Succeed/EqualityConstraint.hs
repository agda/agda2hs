{-# LANGUAGE TypeOperators #-}
module EqualityConstraint where

myFunc :: a ~ b => c
myFunc = error "postulate:   a ~ b => c"

