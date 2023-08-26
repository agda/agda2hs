module Ascending where

open import Haskell.Prelude

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
