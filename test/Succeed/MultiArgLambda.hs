module MultiArgLambda
  (mapMaybeB)
where

mapMaybeB :: (a -> b) -> Maybe a -> Maybe b
mapMaybeB
  = \ x0 x1 ->
      case (x0, x1) of
          (f, Nothing) -> Nothing
          (f, Just x) -> Just (f x)

