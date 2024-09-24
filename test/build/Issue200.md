```haskell
{-# LANGUAGE LambdaCase #-}
module Issue200 where

data Void

test :: Maybe Void -> Maybe Void
test
  = \case
        Nothing -> Nothing

```
