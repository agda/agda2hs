open import Haskell.Prelude

instance
  favoriteNumber : Int
  favoriteNumber = 42
{-# INLINE favoriteNumber #-}

test : {{Int}} → Int
test {{x}} = x
{-# COMPILE AGDA2HS test #-}
