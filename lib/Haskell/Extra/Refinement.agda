module Haskell.Extra.Refinement where

open import Haskell.Prelude
open import Agda.Primitive

private variable
  ℓ ℓ′ : Level

record ∃ (a : Set ℓ) (@0 P : a → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _⟨_⟩
  field
    value    : a
    @0 proof : P value
open ∃ public
{-# COMPILE AGDA2HS ∃ unboxed #-}

mapRefine : {@0 P Q : a → Set ℓ} (@0 f : ∀ {x} → P x → Q x) → ∃ a P → ∃ a Q
mapRefine f (x ⟨ p ⟩) = x ⟨ f p ⟩

{-# COMPILE AGDA2HS mapRefine transparent #-}
