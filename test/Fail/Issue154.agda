module Issue154 where

open import Haskell.Prelude

foo : Nat → Nat
foo zero = zero
foo (suc x) = x
{-# COMPILE AGDA2HS foo #-}
