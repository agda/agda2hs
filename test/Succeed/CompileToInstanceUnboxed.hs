module CompileToInstanceUnboxed
  (test)
where

test :: Bool
test = xy == zw
  where
    xy :: Maybe Int
    xy = Just 1
    zw :: Maybe Int
    zw = Just 2

