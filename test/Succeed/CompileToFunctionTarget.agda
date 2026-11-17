open import Haskell.Prelude

-- The definition of `target` uses a local `where` helper, so it can only be
-- compiled correctly in the context of this module.
target : List Nat → Nat
target xs = go xs
  where
    go : List Nat → Nat
    go [] = 0
    go (x ∷ xs) = x + go xs

{-# COMPILE AGDA2HS target #-}
