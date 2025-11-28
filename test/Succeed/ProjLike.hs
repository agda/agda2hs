module ProjLike where

import Numeric.Natural (Natural)

data Scope a = Empty
             | Bind a (Scope a)

test :: Scope Natural
test = Bind 2 Empty

