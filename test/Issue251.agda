open import Haskell.Prelude

instance
  favoriteNumber : Int
  favoriteNumber = 42
{-# COMPILE AGDA2HS favoriteNumber inline #-}

get : {{Int}} → Int
get {{x}} = x
{-# COMPILE AGDA2HS get #-}

test : Int
test = get
{-# COMPILE AGDA2HS test #-}
