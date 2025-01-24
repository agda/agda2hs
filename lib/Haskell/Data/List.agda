module Haskell.Data.List where

open import Haskell.Prelude

open import Haskell.Data.Ord using (comparing)

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}

partition : (a → Bool) → List a → (List a × List a)
partition p xs = (filter p xs , filter (not ∘ p) xs)

postulate
  sortBy : (a → a → Ordering) → List a → List a

sort : ⦃ Ord a ⦄ → List a → List a
sort = sortBy compare

sortOn : ⦃ Ord b ⦄ → (a → b) → List a → List a
sortOn f =
    map snd
    ∘ sortBy (comparing fst)
    ∘ map (λ x → let y = f x in seq y (y , x))
