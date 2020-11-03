
module Sections where

open import Haskell.Prelude

test₁ : Nat → Nat
test₁ = 5 +_

test₂ : Nat → Nat
test₂ = _+ 5

test₃ : Nat → Nat
test₃ = _+_ 5

{-# COMPILE AGDA2HS test₁ #-}
{-# COMPILE AGDA2HS test₂ #-}
{-# COMPILE AGDA2HS test₃ #-}
