module Haskell.Prim.Maybe where

open import Haskell.Prim

--------------------------------------------------
-- Maybe

data Maybe {@0 ℓ} (a : Type ℓ) : Type ℓ where
  Nothing : Maybe a
  Just    : a -> Maybe a

maybe : ∀ {@0 ℓ₁ ℓ₂} {@0 a : Type ℓ₁} {@0 b : Type ℓ₂} → b → (a → b) → Maybe a → b
maybe n j Nothing  = n
maybe n j (Just x) = j x
