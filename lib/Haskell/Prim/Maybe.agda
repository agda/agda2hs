
module Haskell.Prim.Maybe where

--------------------------------------------------
-- Maybe

data Maybe {@0 ℓ} (a : Set ℓ) : Set ℓ where
  Nothing : Maybe a
  Just    : a -> Maybe a

maybe : ∀ {@0 ℓ₁ ℓ₂} {@0 a : Set ℓ₁} {@0 b : Set ℓ₂} → b → (a → b) → Maybe a → b
maybe n j Nothing  = n
maybe n j (Just x) = j x
