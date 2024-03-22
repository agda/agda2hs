```haskell
module Issue93 where

fun :: Bool -> Bool
fun x
  = case x of
        True -> False
        False -> y
  where
    y :: Bool
    y = True

nested :: Maybe Bool -> Bool
nested x
  = case x of
        Just b -> case y of
                      True -> b
                      False -> z
        Nothing -> y
  where
    y :: Bool
    y = True
    z :: Bool
    z = case y of
            True -> y
            False -> True

```
