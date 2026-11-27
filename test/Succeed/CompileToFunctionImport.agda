open import Haskell.Prelude
open import CompileToFunctionTarget

source : List Nat → Nat
source xs = go xs
  where
    go : List Nat → Nat
    go [] = 0
    go (x ∷ xs) = x + go xs

{-# COMPILE AGDA2HS source to target #-}

test : List Nat → Nat
test = source

{-# COMPILE AGDA2HS test #-}
