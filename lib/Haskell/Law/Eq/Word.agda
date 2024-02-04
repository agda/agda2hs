module Haskell.Law.Eq.Word where

open import Agda.Builtin.Word.Properties renaming (primWord64ToNatInjective to w2n-injective)

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Word

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Nat
open import Haskell.Law.Equality

instance
  iLawfulEqWord : IsLawfulEq Word
  iLawfulEqWord .isEquality x y with (w2n x) in h₁ | (w2n y) in h₂ 
  ... | a | b  = mapReflects
    (λ h → w2n-injective x y $ sym $ trans (trans h₂ $ sym h) (sym h₁))
    (λ h → trans (sym $ trans (cong w2n (sym h)) h₁) h₂)
    (isEquality a b)
