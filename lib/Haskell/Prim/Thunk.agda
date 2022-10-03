{-# OPTIONS --sized-types #-}

module Haskell.Prim.Thunk where

open import Agda.Builtin.Size public

open import Haskell.Prim

record Thunk {ℓ} (a : Size → Set ℓ) (i : Size) : Set ℓ where
  constructor delay
  coinductive
  field force : {j : Size< i} → a j
open Thunk public

{-# COMPILE AGDA2HS Thunk unboxed #-}
