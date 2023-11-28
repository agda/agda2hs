module Fail.Issue142 where

open import Haskell.Prelude

-- `coerce` is a primitive but this general structure remains disallowed
falseCoerce : @0 a ≡ b → a → b
falseCoerce refl x = x
{-# COMPILE AGDA2HS falseCoerce #-}
