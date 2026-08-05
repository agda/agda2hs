
module Haskell.Prim.List where

open import Haskell.Prim

--------------------------------------------------
-- List

infixr 5 _++_
_++_ : ∀ {@0 ℓ} {@0 a : Type ℓ} → List a → List a → List a
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

head : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → a
head (x ∷ _) = x

last : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → a
last (x ∷ [])         = x
last (_ ∷ xs@(_ ∷ _)) = last xs

tail : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → List a
tail (_ ∷ xs) = xs

init : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → List a
init (x ∷ [])         = []
init (x ∷ xs@(_ ∷ _)) = x ∷ init xs

map : (a → b) → List a → List b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

lengthNat : List a → Nat
lengthNat []       = 0
lengthNat (_ ∷ xs) = addNat 1 (lengthNat xs)
