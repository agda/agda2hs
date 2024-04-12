```haskell
module NonClassInstance where

iDecIsTrue :: Bool -> Bool
iDecIsTrue False = False
iDecIsTrue True = True

foo :: Bool -> Bool -> Bool
foo _ b = not b

bar :: Bool -> Bool
bar b = foo b (iDecIsTrue b)

```
