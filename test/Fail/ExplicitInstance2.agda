
module Fail.ExplicitInstance2 where

open import Haskell.Prelude

record HasDefault (a : Type) : Type where
  field
    theDefault : a
open HasDefault {{...}}
{-# COMPILE AGDA2HS HasDefault class #-}

-- This should be an error even if there is no instance in scope
test : Bool
test = theDefault {{λ where .theDefault → True}}
{-# COMPILE AGDA2HS test #-}
