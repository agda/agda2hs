module Haskell.Law.Eq.List where

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality
open import Haskell.Law.List

isEqualityList : ⦃ iEqA : Eq a ⦄ → ⦃ IsLawfulEq a ⦄ → ∀ (x y : List a) → Reflects (x ≡ y) (x == y)
isEqualityList [] [] = refl
isEqualityList [] (x ∷ y) = λ ()
isEqualityList (x ∷ x₁) [] = λ ()
isEqualityList (x ∷ xs) (y ∷ ys) with (x == y) in h₁
... | True = mapReflects 
    (λ h → cong₂ (_∷_) (equality x y h₁)  h) 
    ∷-injective-right 
    (isEqualityList xs ys)
... | False = λ h → (nequality x y h₁) (∷-injective-left h)


instance
  iLawfulEqList : ⦃ iEqA : Eq a ⦄ → ⦃ IsLawfulEq a ⦄ → IsLawfulEq (List a)
  iLawfulEqList = λ where       
    .isEquality -> isEqualityList
