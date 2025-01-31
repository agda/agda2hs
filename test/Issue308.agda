open import Haskell.Prelude

record Class (a : Type) : Type where
  field
    foo : a → a
open Class {{...}} public
{-# COMPILE AGDA2HS Class class #-}

module M1 (@0 X : Type) where

  instance
    ClassInt : Class Int
    ClassInt .foo = _+ 1
  {-# COMPILE AGDA2HS ClassInt #-}

module M2 (@0 X : Type) where

  open M1 X

  tester : Int
  tester = foo 41
  {-# COMPILE AGDA2HS tester #-}
