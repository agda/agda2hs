
module Fail.NonCanonicalSuperclass where

open import Haskell.Prelude

record Class (a : Type) : Type where
  field
    foo : a → a
open Class {{...}} public

{-# COMPILE AGDA2HS Class class #-}

instance
  ClassBool : Class Bool
  ClassBool .foo = not

{-# COMPILE AGDA2HS ClassBool #-}

record Subclass (a : Type) : Type where
  field
    overlap {{super}} : Class a
    bar : a
open Subclass {{...}} public

{-# COMPILE AGDA2HS Subclass class #-}

instance
  SubclassBool : Subclass Bool
  SubclassBool .super = record { foo = id }
  SubclassBool .bar = False

{-# COMPILE AGDA2HS SubclassBool #-}
