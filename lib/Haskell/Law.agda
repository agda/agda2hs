module Haskell.Law where

open import Haskell.Prim
open import Haskell.Prim.Bool

ifFlip : ∀ (b) (t e : a) → (if b then t else e) ≡ (if not b then e else t)
ifFlip False _ _ = refl
ifFlip True  _ _ = refl
