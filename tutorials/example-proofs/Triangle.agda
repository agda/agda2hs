module Triangle where

open import Haskell.Prelude

-- helper function
countBiggerThan : ⦃ Ord a ⦄ → List a → a → Int 
countBiggerThan xs b = length (filter (λ x → (x >= b)) xs)

{-# COMPILE AGDA2HS countBiggerThan #-}

-- Triangle data type deinfition
data Triangle : Set where
    MkTriangle : (alpha beta gamma : Nat)
        → ⦃ @0 h₁ : (((alpha + beta + gamma) == 180) ≡ True ) ⦄
        → @0 ⦃ ((countBiggerThan
     (alpha ∷ beta ∷  gamma ∷ []) 90 <= 1) ≡ True ) ⦄
           → Triangle

{-# COMPILE AGDA2HS Triangle #-}

-- first alternative constructing function
createTriangle : Nat -> Nat -> Nat -> Maybe Triangle
createTriangle alpha beta gamma 
    = if (countBiggerThan (alpha ∷ beta ∷  gamma ∷ []) 90 <= 1)
        then if (alpha + beta + gamma == 180 )
            then Just (MkTriangle alpha beta gamma) 
            else Nothing
        else Nothing

{-# COMPILE AGDA2HS createTriangle #-}

-- second alternative constructing funtion
createTriangle₁ : Nat -> Nat -> Nat -> Maybe Triangle
createTriangle₁ alpha beta gamma 
    = if ((countBiggerThan (alpha ∷ beta ∷  gamma ∷ []) 90 <= 1) && (alpha + beta + gamma == 180 )) 
        then (λ ⦃ h₁ ⦄ →  Just (MkTriangle alpha beta gamma 
            ⦃ &&-rightTrue h₁ ⦄ 
            ⦃ &&-leftTrue h₁ ⦄) )
        else Nothing
 
{-# COMPILE AGDA2HS createTriangle₁ #-}
