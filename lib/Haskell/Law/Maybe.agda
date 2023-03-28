module Haskell.Law.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

injective : ∀ {x y : a} → Just x ≡ Just y → x ≡ y
injective refl = refl
