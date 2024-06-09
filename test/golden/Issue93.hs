module Issue93 where

fun :: Bool -> Bool
fun x =
  if x then False else y
  where
    y :: Bool
    y = True

nested :: Maybe Bool -> Bool
nested x =
  case x of
    Just b -> (if y then b else z)
    Nothing -> y
  where
    y :: Bool
    y = True
    z :: Bool
    z = if y then y else True
