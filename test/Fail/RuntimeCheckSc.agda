module Fail.RuntimeCheckSc where

open import Haskell.Prelude

data Dat : Set where
  Conflict : ((x : Nat) ⦃@0 _ : IsTrue (x > 0)⦄ → Nat) → Dat
{-# COMPILE AGDA2HS Dat #-}

scConflict : Nat
scConflict = 0
{-# COMPILE AGDA2HS scConflict #-}
