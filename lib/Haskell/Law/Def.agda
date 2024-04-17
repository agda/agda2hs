module Haskell.Law.Def where

open import Haskell.Prim

Injective : (a → b) → Set _
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

F-sym : (a → a → b) → Set _ 
F-sym f = ∀ x y → f x y ≡ f y x
