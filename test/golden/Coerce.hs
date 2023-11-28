module Coerce where

import Numeric.Natural (Natural)
import Unsafe.Coerce (unsafeCoerce)

newtype A = MkA Natural

newtype B = MkB Natural
              deriving (Show)

coerceExample :: B
coerceExample = unsafeCoerce (MkA 5)

