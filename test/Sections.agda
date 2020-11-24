
module Sections where

open import Haskell.Prelude
open import Agda.Builtin.Nat

test₁ : Nat → Nat
test₁ = 5 +_

test₂ : Nat → Nat
test₂ = _+ 5

test₃ : Nat → Nat
test₃ = _+_ 5

test₄ : Nat → Nat
test₄ = λ x → x + 5

test₅ : Nat → Nat
test₅ = λ x → 5 + x -- Agda eta-contracts this before we get to see it

{-# COMPILE AGDA2HS test₁ #-}
{-# COMPILE AGDA2HS test₂ #-}
{-# COMPILE AGDA2HS test₃ #-}
{-# COMPILE AGDA2HS test₄ #-}
{-# COMPILE AGDA2HS test₅ #-}
