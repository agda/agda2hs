```haskell
{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
module Issue145 where

it :: forall a . a -> a
it x = x

it' :: Monoid a => a -> a
it' x = x

data Ok' a = Thing' !a

data Ok a = Thing a

test :: Ok String
test = Thing "ok"

```
