open import Haskell.Prelude

record HasDefault (a : Type) : Type where
  field
    theDefault : a
open HasDefault {{...}}
{-# COMPILE AGDA2HS HasDefault class #-}

instance
  defaultBool : HasDefault Bool
  defaultBool .theDefault = False
{-# COMPILE AGDA2HS defaultBool instance #-}

test : Bool
test = theDefault
{-# COMPILE AGDA2HS test #-}
