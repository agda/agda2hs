open import Haskell.Prelude

module Fail.Issue306b where

record Foo (a b : Set) : Set where
  no-eta-equality
  field
    coe : a → b
open Foo public

instance
  foo : ∀ {a b : Set} → {{@0 _ : a ≡ b}} → Foo a b
  foo {{refl}} .coe x = x

{-# COMPILE AGDA2HS Foo class #-}
{-# COMPILE AGDA2HS foo #-}
