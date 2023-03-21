module Haskell.Law.List where

open import Haskell.Prim
open import Haskell.Prim.List

--------------------------------------------------
-- ++

++-[] : ∀ (xs : List a) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (x ∷ xs) rewrite ++-[] xs = refl
