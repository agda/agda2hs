module Fail.Issue142 where

open import Haskell.Prelude

coerce : @0 a ≡ b → a → b
coerce refl x = x
{-# COMPILE AGDA2HS coerce #-}
