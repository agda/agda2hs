module Haskell.Extra.Refinement where

open import Haskell.Prelude
open import Agda.Primitive

private variable
  ℓ ℓ′ : Level

record ∃ (@0 a : Set ℓ) (@0 P : a → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _⟨_⟩
  field
    value    : a
    @0 proof : P value
open ∃ public
{-# COMPILE AGDA2HS ∃ unboxed #-}
