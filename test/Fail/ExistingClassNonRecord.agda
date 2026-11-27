-- See PR #446: `existing-class` can only be applied to records.
module ExistingClassNonRecord where

open import Haskell.Prelude

foo : Nat
foo = 0
{-# COMPILE AGDA2HS foo existing-class #-}
