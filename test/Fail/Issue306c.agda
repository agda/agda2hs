open import Haskell.Prelude

module Fail.Issue306c where

record Foo (a b : Set) : Set where
  no-eta-equality
  field
    coe : a → b
open Foo public

module _ {a b : Set} where
  instance
    foo : {{@0 _ : a ≡ b}} → Foo a b
    foo {{refl}} .coe x = x

{-# COMPILE AGDA2HS Foo class #-}
{-# COMPILE AGDA2HS foo #-}
