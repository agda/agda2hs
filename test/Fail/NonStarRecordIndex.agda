module Fail.NonStarRecordIndex where

open import Haskell.Prelude

record T (n : Nat) : Set where
  field
    Tb : Bool
{-# COMPILE AGDA2HS T #-}
