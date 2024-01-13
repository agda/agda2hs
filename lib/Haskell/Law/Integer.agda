module Haskell.Law.Integer where

open import Haskell.Prim

pos-injective : ∀ { a b : Nat } → pos a ≡ pos b → a ≡ b
pos-injective refl = refl

neg-injective : ∀ { a b : Nat } → negsuc a ≡ negsuc b → a ≡ b
neg-injective refl = refl
