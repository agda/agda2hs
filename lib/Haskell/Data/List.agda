module Haskell.Data.List where

open import Haskell.Prelude

open import Haskell.Data.Ord using (comparing)

open import Haskell.Law.Eq
open import Haskell.Law.Equality

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}

partition : (a → Bool) → List a → (List a × List a)
partition p xs = (filter p xs , filter (not ∘ p) xs)

deleteBy : (a → a → Bool) → a → List a → List a
deleteBy eq x ys = filter (not ∘ (eq x)) ys

delete : ⦃ Eq a ⦄ → a → List a → List a
delete = deleteBy (_==_)

-- | These semantics of 'nub' assume that the 'Eq' instance
-- is lawful.
-- These semantics are inefficient, but good for proofs.
nub : ⦃ _ : Eq a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → List a → List a
nub [] = []
nub (x ∷ xs) = x ∷ delete x (nub xs)

postulate
  sortBy : (a → a → Ordering) → List a → List a

sort : ⦃ Ord a ⦄ → List a → List a
sort = sortBy compare

sortOn : ⦃ Ord b ⦄ → (a → b) → List a → List a
sortOn f =
    map snd
    ∘ sortBy (comparing fst)
    ∘ map (λ x → let y = f x in seq y (y , x))
