module Haskell.Law where

open import Haskell.Prim
open import Haskell.Prim.Bool

ifFlip : ∀ (b) (t e : a) → (if b then t else e) ≡ (if not b then e else t)
ifFlip False _ _ = refl
ifFlip True  _ _ = refl

ifTrueEqThen : ∀ (b : Bool) {thn els : a} → b ≡ True → (if b then thn else els) ≡ thn
ifTrueEqThen .True refl = refl

ifFalseEqElse : ∀ (b : Bool) {thn els : a} → b ≡ False → (if b then thn else els) ≡ els
ifFalseEqElse .False refl = refl
