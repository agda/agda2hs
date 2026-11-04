module EqualityConstraint
  (myFunc)
where

myFunc :: a ~ b => c
myFunc = error "postulate:   a ~ b => c"

