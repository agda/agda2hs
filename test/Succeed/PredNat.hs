module PredNat where

import Numeric.Natural (Natural)

predNat' :: Natural -> Natural
predNat' n = pred n

recNat :: a -> (Natural -> a -> a) -> Natural -> a
recNat z s n
  = if n == 0 then z else
      case pred n of
          m -> s m (recNat z s m)

