module ClassMayThrow where

open import Haskell.Prelude
open import Haskell.Control.Exception
open import Haskell.Extra.Dec

-- A class method may return a value that may throw.
record Checked (a : Set) : Set where
  field
    checked : a → MayThrow AssertionFailed a
open Checked public
{-# COMPILE AGDA2HS Checked class #-}

instance
  iCheckedNat : Checked Nat
  iCheckedNat .checked x = assert (IsTrue (x == 0)) x
{-# COMPILE AGDA2HS iCheckedNat #-}
