module Fail.RuntimeCheckInline where

open import Haskell.Prelude

inlinable : Nat
inlinable = 0
{-# COMPILE AGDA2HS inlinable inline #-}

notInlinable : (x : Nat) → ⦃@0 _ : IsTrue (x > 0)⦄ → Nat
notInlinable _ = 0
{-# COMPILE AGDA2HS notInlinable inline #-}
