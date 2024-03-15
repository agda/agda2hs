open import Haskell.Prelude

module Issue305 (@0 X : Set) where

record Class (a : Set) : Set where
  field
    foo : a → a
open Class {{...}} public

{-# COMPILE AGDA2HS Class class #-}

instance
  ClassInt : Class Int
  ClassInt .foo = _+ 1

{-# COMPILE AGDA2HS ClassInt #-}

test : Int
test = foo 41

{-# COMPILE AGDA2HS test #-}
