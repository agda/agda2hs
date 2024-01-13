module Haskell.Law.Int where

open import Haskell.Prim
open import Haskell.Prim.Int

int64-injective : ∀ {a b : Word64} → (int64 a) ≡ (int64 b) → a ≡ b
int64-injective refl = refl 
