module Haskell.Law.Nat where

open import Haskell.Prim

suc-injective : ∀ { a b : Nat } → suc a ≡ suc b → a ≡ b
suc-injective refl = refl
