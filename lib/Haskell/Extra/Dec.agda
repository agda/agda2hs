module Haskell.Extra.Dec where

open import Haskell.Prelude hiding (Reflects)
open import Agda.Primitive

@0 Reflects : ∀ {ℓ} → Set ℓ → Bool → Set ℓ
Reflects P True  = P
Reflects P False = P → ⊥

record ∃ {ℓ ℓ′} (@0 a : Set ℓ) (@0 P : a → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _⟨_⟩
  field
    value    : a
    @0 proof : P value
open ∃ public
{-# COMPILE AGDA2HS ∃ unboxed #-}

Dec : ∀ {ℓ} → @0 Set ℓ → Set ℓ
Dec P = ∃ Bool (Reflects P)
{-# COMPILE AGDA2HS Dec #-}

mapDec : @0 (a → b)
       → @0 (b → a)
       → Dec a → Dec b
mapDec f g (True  ⟨ x ⟩) = True  ⟨ f x   ⟩
mapDec f g (False ⟨ h ⟩) = False ⟨ h ∘ g ⟩
{-# COMPILE AGDA2HS mapDec transparent #-}
