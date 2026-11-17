module MultiArgumentPatternLambda
  (tooManyPats)
where

tooManyPats :: Bool -> Bool -> Bool
tooManyPats
  = \ x0 x1 ->
      case (x0, x1) of
          (False, False) -> False
          (True, True) -> False
          (_, _) -> True

