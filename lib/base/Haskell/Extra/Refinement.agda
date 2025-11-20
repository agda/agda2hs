module Haskell.Extra.Refinement where

open import Haskell.Prim
open import Haskell.Prim.Maybe

record ∃ (a : Type ℓ) (@0 P : a → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  constructor _⟨⟩
  field
    value    : a
    @0 {{proof}} : P value
open ∃ public
{-# COMPILE AGDA2HS ∃ unboxed #-}

pattern _⟨_⟩ x p = (x ⟨⟩) {{p}}

mapRefine : {@0 P Q : a → Type ℓ} (@0 f : ∀ {x} → P x → Q x) → ∃ a P → ∃ a Q
mapRefine f (x ⟨ p ⟩) = x ⟨ f p ⟩

{-# COMPILE AGDA2HS mapRefine transparent #-}

refineMaybe : {@0 P : a → Type ℓ}
            → (mx : Maybe a) → @0 (∀ {x} → mx ≡ Just x → P x)
            → Maybe (∃ a P)
refineMaybe Nothing f = Nothing
refineMaybe (Just x) f = Just (x ⟨ f refl ⟩)

{-# COMPILE AGDA2HS refineMaybe transparent #-}
