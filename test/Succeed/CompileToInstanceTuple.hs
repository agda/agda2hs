module CompileToInstanceTuple
  (test)
where

test :: Bool
test = xy == zw
  where
    xy :: (Int, Int)
    xy = (1, 2)
    zw :: (Int, Int)
    zw = (1, 3)

