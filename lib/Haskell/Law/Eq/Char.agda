module Haskell.Law.Eq.Char where

open import Agda.Builtin.Char.Properties  renaming (primCharToNatInjective to c2n-injective)

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Nat
open import Haskell.Law.Equality

instance
  iLawfulEqChar : IsLawfulEq Char
  iLawfulEqChar .isEquality x y with (c2n x) in h₁ | (c2n y) in h₂ 
  ... | a | b  = mapReflects { a ≡ b } { x ≡ y } { eqNat a b } 
    (λ h → c2n-injective x y $ sym $ trans (trans h₂ $ sym h) (sym h₁))
    (λ h → trans (sym $ trans (cong c2n (sym h)) h₁) h₂)
    (isEquality a b)
