module Haskell.Data.List where

open import Haskell.Prelude

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}

partition : (a → Bool) → List a → (List a × List a)
partition p xs = (filter p xs , filter (not ∘ p) xs)

