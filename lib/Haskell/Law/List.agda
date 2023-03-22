module Haskell.Law.List where

open import Haskell.Prim
open import Haskell.Prim.List

--------------------------------------------------
-- ++

++-[] : ∀ (xs : List a) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (x ∷ xs) rewrite ++-[] xs = refl

[]-++ : ∀ (xs : List a) → xs ++ [] ≡ xs
[]-++ [] = refl
[]-++ (x ∷ xs) rewrite []-++ xs = refl

++-assoc : ∀ (xs ys zs : List a) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl
