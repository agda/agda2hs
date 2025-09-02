-- Copatterns are not supported, except in specific cases

module Fail.Copatterns where

open import Haskell.Prelude

record R : Type where
  no-eta-equality
  field
    foo : Bool
open R public

{-# COMPILE AGDA2HS R #-}

test : R
test .foo = True

{-# COMPILE AGDA2HS test #-}
