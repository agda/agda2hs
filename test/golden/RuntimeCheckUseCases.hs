module RuntimeCheckUseCases (RuntimeCheckUseCases.subtractFromGreater, RuntimeCheckUseCases.headOfNonEmpty) where

import Haskell.Extra.Dec.Instances (decIsFalse, decNonEmpty)
import Numeric.Natural (Natural)

import RuntimeCheckUseCases.PostRtc

subtractFromGreater :: Natural -> Natural -> Natural
subtractFromGreater x y
  | decIsFalse (x < y) =
    RuntimeCheckUseCases.PostRtc.subtractFromGreater x y
  | otherwise = error "Runtime check failed: decIsFalse (x < y)"

headOfNonEmpty :: [Natural] -> Natural
headOfNonEmpty xs
  | decNonEmpty xs = RuntimeCheckUseCases.PostRtc.headOfNonEmpty xs
  | otherwise = error "Runtime check failed: decNonEmpty xs"

