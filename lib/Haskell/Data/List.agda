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

-- | Delete all occurrences of an item.
-- Not part of 'Data.List'.
deleteAll : ⦃ _ : Eq a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → a → List a → List a
deleteAll x = filter (not ∘ (x ==_))

-- | These semantics of 'nub' assume that the 'Eq' instance
-- is lawful.
-- These semantics are inefficient, but good for proofs.
nub : ⦃ _ : Eq a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → List a → List a
nub [] = []
nub (x ∷ xs) = x ∷ deleteAll x (nub xs)

postulate
  sortBy : (a → a → Ordering) → List a → List a

sort : ⦃ Ord a ⦄ → List a → List a
sort = sortBy compare

sortOn : ⦃ Ord b ⦄ → (a → b) → List a → List a
sortOn f =
    map snd
    ∘ sortBy (comparing fst)
    ∘ map (λ x → let y = f x in seq y (y , x))

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}

-- | A deleted item is no longer an element.
--
prop-elem-deleteAll
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x y : a) (zs : List a)
  → elem x (deleteAll y zs)
    ≡ (if x == y then False else elem x zs)
--
prop-elem-deleteAll x y []
  with x == y
... | False = refl
... | True  = refl
prop-elem-deleteAll x y (z ∷ zs)
  with recurse ← prop-elem-deleteAll x y zs
  with y == z in eqyz
... | True
    with x == z in eqxz
...   | True
      rewrite equality' _ _ (trans (equality x z eqxz) (sym (equality y z eqyz)))
      = recurse
...   | False
      = recurse
prop-elem-deleteAll x y (z ∷ zs)
    | False
    with x == z in eqxz
...   | True
      rewrite equality x z eqxz | eqSymmetry y z | eqyz
      = refl
...   | False
      = recurse

-- | An item is an element of the 'nub' iff it is
-- an element of the original list.
--
prop-elem-nub
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x : a) (ys : List a)
  → elem x (nub ys)
    ≡ elem x ys
--
prop-elem-nub x [] = refl
prop-elem-nub x (y ∷ ys)
  rewrite prop-elem-deleteAll x y (nub ys)
  with x == y
... | True = refl
... | False = prop-elem-nub x ys
