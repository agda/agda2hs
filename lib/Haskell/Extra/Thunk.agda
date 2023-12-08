{-# OPTIONS --sized-types #-}

module Haskell.Extra.Thunk where

open import Agda.Builtin.Size public

open import Haskell.Prim

record Thunk {ℓ} (a : @0 Size → Set ℓ) (@0 i : Size) : Set ℓ where
  constructor delay
  coinductive
  field force : {@0 j : Size< i} → a j
open Thunk public

{-# COMPILE AGDA2HS Thunk unboxed #-}
