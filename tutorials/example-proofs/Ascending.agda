module Ascending where

open import Haskell.Prelude
open import Haskell.Prim 

-- function judging ascending order on lists
isAscending : ⦃ iOrdA : Ord a ⦄ → List a → Bool
isAscending [] = True
isAscending (x ∷ []) = True
isAscending (x ∷ y ∷ xs) = if x <= y then isAscending (y ∷ xs) else False

{-# COMPILE AGDA2HS isAscending #-}

-- data type defining a postulate of ascending order on lists
data IsAscending₂ {a : Set} ⦃ iOrdA : Ord a ⦄ : List a → Set where
    Empty : IsAscending₂ []
    OneElem : (x : a) →  IsAscending₂ (x ∷ [])
    ManyElem : (x y : a) (xs : List a) 
        → ⦃ IsAscending₂ (y ∷ xs) ⦄
        → ⦃ IsTrue (x <= y) ⦄
        → IsAscending₂ (x ∷ y ∷ xs)

-- helpers for transition between different expressions of truth
useEq : {x y : Bool} → x ≡ y → IsTrue x → IsTrue y
useEq {True} {True} eq is = IsTrue.itsTrue

reverseEq : { x : Bool } → (IsTrue x) → x ≡ True
reverseEq {False} ()
reverseEq {True} input = refl 


-- proof for predicte holds → (function is true)
theorem₁ : ⦃ iOrdA : Ord a ⦄ (xs : List a) → ⦃ IsAscending₂ xs ⦄ → (IsTrue (isAscending xs)) 
theorem₁ [] = IsTrue.itsTrue 
theorem₁ (x ∷ []) = IsTrue.itsTrue
theorem₁ (x ∷ x₁ ∷ xs) ⦃ (ManyElem .x .x₁ .xs ⦃ h₁ ⦄ ⦃ h₂ ⦄) ⦄ = useEq ( sym $
    begin
        isAscending (x ∷ x₁ ∷ xs)
    ≡⟨⟩ 
        (if x <= x₁ then isAscending (x₁ ∷ xs) else False)
    ≡⟨ ifTrueEqThen (x <= x₁)  (reverseEq h₂) ⟩ 
        isAscending (x₁ ∷ xs)
    ≡⟨ reverseEq (theorem₁ (x₁ ∷ xs) ) ⟩ 
        True
    ∎ ) IsTrue.itsTrue

--reductio ad absurdum
absurd₁ : {x : Bool} → (x ≡ True) → (x ≡ False) → ⊥
absurd₁ {False} () b 
absurd₁ {True} a ()

--inductive hypothesis for isAscending function
helper₁ : ⦃ iOrdA : Ord a ⦄ (x : a) (xs : List a) → isAscending xs ≡ False → (isAscending (x ∷ xs)) ≡ False
helper₁ x xs h₁ with (isAscending (x ∷ xs)) in h₂
helper₁ x (x₁ ∷ xs) h₁ | True  with (x <= x₁)
helper₁ x (x₁ ∷ xs) h₁ | True | True = magic (absurd₁ h₂ h₁)
helper₁ x (x₁ ∷ xs) h₁ | True | False = sym h₂
helper₁ x xs h₁ | False = refl

--recursion helper
postulate
   theorem₂helper : ⦃ iOrdA : Ord a ⦄ (xs : List a) 
    → (IsTrue (isAscending xs)) → IsAscending₂ xs

--proof for (function returns true) → predicate holds version 1 (wrong)
theorem₂ : ⦃ iOrdA : Ord a ⦄ (xs : List a) 
    → (IsTrue (isAscending xs)) → IsAscending₂ xs
theorem₂ [] h₁ = Empty
theorem₂ (x ∷ []) h₁ = OneElem x
theorem₂ (x ∷ x₁ ∷ xs) h₁ with (isAscending xs) in h₂ | (x <= x₁) in h₃
theorem₂ (x ∷ x₁ ∷ xs) h₁ | True  | True = ManyElem x x₁ xs  
    ⦃ theorem₂helper (x₁ ∷ xs) h₁ ⦄ ⦃ useEq ( sym $ h₃ ) IsTrue.itsTrue ⦄
theorem₂ (x ∷ x₁ ∷ xs) () | _     | False 
theorem₂ (x ∷ x₁ ∷ xs) h₁ | False | True = magic (
         absurd₁ (reverseEq h₁) (helper₁ x₁ xs h₂) )

helper₂ : ⦃ iOrdA : Ord a ⦄ (x : a) (xs : List a) 
    → (IsTrue (isAscending (x ∷ xs))) → (IsTrue (isAscending xs))
helper₂ x [] h₁ = IsTrue.itsTrue
helper₂ x (x₁ ∷ xs) h₁ with (x <= x₁) in h₂
helper₂ x (x₁ ∷ xs) h₁ | True = h₁
helper₂ x (x₁ ∷ xs) () | False 

--proof for (function returns true) → predicate holds version 2
theorem₃ : ⦃ iOrdA : Ord a ⦄ (xs : List a) 
    → (IsTrue (isAscending xs)) → IsAscending₂ xs
theorem₃ [] h₁ = Empty
theorem₃ (x ∷ []) h₁ = OneElem x
theorem₃ (x ∷ x₁ ∷ xs) h₁ with (theorem₃ (x₁ ∷ xs) (helper₂ x (x₁ ∷ xs) h₁)) 
theorem₃ (x ∷ x₁ ∷ xs) h₁ | _ with (x <= x₁) in h₂ 
theorem₃ (x ∷ x₁ ∷ xs) h₁ | h₃ | True  = ManyElem x x₁ xs 
    ⦃ h₃ ⦄ ⦃ useEq ( sym $ h₂ ) IsTrue.itsTrue ⦄
theorem₃ (x ∷ x₁ ∷ xs) () | _  | False  
