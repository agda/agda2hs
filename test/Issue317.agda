open import Haskell.Prelude

record D : Type where
  constructor C
  field unC : Int
open D public
{-# COMPILE AGDA2HS D #-}

test : D → D
test d = C ∘ unC $ d
{-# COMPILE AGDA2HS test #-}
