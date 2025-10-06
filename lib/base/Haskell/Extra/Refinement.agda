module Haskell.Extra.Refinement where

open import Haskell.Prelude
open import Agda.Primitive

private variable
  ℓ ℓ′ : Level

record ∃ (a : Type ℓ) (@0 P : a → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  constructor _⟨_⟩
  field
    value    : a
    @0 proof : P value
open ∃ public
{-# COMPILE AGDA2HS ∃ unboxed #-}

_⟨⟩ : {@0 P : a → Type ℓ} (x : a) → @0 {{P x}} → ∃ a P
(x ⟨⟩) {{p}} = x ⟨ p ⟩

{-# COMPILE AGDA2HS _⟨⟩ inline #-}

mapRefine : {@0 P Q : a → Type ℓ} (@0 f : ∀ {x} → P x → Q x) → ∃ a P → ∃ a Q
mapRefine f (x ⟨ p ⟩) = x ⟨ f p ⟩

{-# COMPILE AGDA2HS mapRefine transparent #-}

refineMaybe : {@0 P : a → Type ℓ}
            → (mx : Maybe a) → @0 (∀ {x} → mx ≡ Just x → P x)
            → Maybe (∃ a P)
refineMaybe Nothing f = Nothing
refineMaybe (Just x) f = Just (x ⟨ f refl ⟩)

{-# COMPILE AGDA2HS refineMaybe transparent #-}
