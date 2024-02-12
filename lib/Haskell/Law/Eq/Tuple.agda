module Haskell.Law.Eq.Tuple where
    
open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Tuple 

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality


instance
    iLawfulEqTuple₂ : ⦃ iEqA : Eq a ⦄ ⦃ iEqB : Eq b ⦄
                → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄
                → IsLawfulEq (a × b)
    iLawfulEqTuple₂ .isEquality (x₁ , x₂) (y₁ , y₂) with (x₁ == y₁) in h₁
    ... | True  = mapReflects
        (λ h → cong₂ _,_ (equality x₁ y₁ h₁) h) 
        (cong snd) 
        (isEquality x₂ y₂)
    ... | False = λ h → exFalso (equality' x₁ y₁ (cong fst h)) h₁


    iLawfulEqTuple₃ : ⦃ iEqA : Eq a ⦄ ⦃ iEqB : Eq b ⦄ ⦃ iEqC : Eq c ⦄
                    → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄ → ⦃ IsLawfulEq c ⦄
                    → IsLawfulEq (a × b × c)
    iLawfulEqTuple₃ .isEquality (x₁ , x₂ , x₃) (y₁ , y₂ , y₃) with (x₁ == y₁) in h₁ 
    ... | True  = mapReflects
        (λ h → cong₂ (λ a (b , c) → a , b , c) (equality x₁ y₁ h₁) h) 
        (cong λ h → snd₃ h , thd₃ h) 
        (isEquality (x₂ , x₃) (y₂ , y₃))
    ... | False = λ h → exFalso (equality' x₁ y₁ (cong  fst₃ h)) h₁ 
