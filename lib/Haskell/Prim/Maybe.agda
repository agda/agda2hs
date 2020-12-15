
module Haskell.Prim.Maybe where

private
  variable a b : Set

--------------------------------------------------
-- Maybe

data Maybe {ℓ} (a : Set ℓ) : Set ℓ where
  Nothing : Maybe a
  Just    : a -> Maybe a

maybe : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → b → (a → b) → Maybe a → b
maybe n j Nothing  = n
maybe n j (Just x) = j x
