{-# OPTIONS --prop --sized-types #-}

open import Agda.Primitive
open import Agda.Builtin.Size
open import Haskell.Prelude

data P : Prop where

record R : Type where
  field
    @0 anErasedThing : Bool
    aRealThing : Int
    aLevel : Level
    aProp : P
    aSize : Size
open R public

{-# COMPILE AGDA2HS R unboxed #-}

foo : R → Int
foo = aRealThing

{-# COMPILE AGDA2HS foo #-}
