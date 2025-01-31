module Haskell.Law.Def where

open import Haskell.Prim

Injective : (a → b) → Type _
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y
