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

instance
  ClassBool : Class Bool
  ClassBool .foo = not

{-# COMPILE AGDA2HS ClassBool #-}

test : Int
test = foo 41

{-# COMPILE AGDA2HS test #-}

anotherTest : Int
anotherTest = test

{-# COMPILE AGDA2HS anotherTest #-}

yetAnotherTest : Int
yetAnotherTest = case Just True of λ where
  Nothing → error "unreachable"
  (Just y) → foo 5
{-# COMPILE AGDA2HS yetAnotherTest #-}

andOneMoreTest : Int → Int
andOneMoreTest x = foo 5
{-# COMPILE AGDA2HS andOneMoreTest #-}

record Subclass (a : Set) : Set where
  field
    overlap {{super}} : Class a
    bar : a
open Subclass {{...}} public

{-# COMPILE AGDA2HS Subclass class #-}

instance 
  SubclassBool : Subclass Bool
  SubclassBool .super = ClassBool
  SubclassBool .bar = False

{-# COMPILE AGDA2HS SubclassBool #-}
