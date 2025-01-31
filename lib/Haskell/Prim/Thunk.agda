{-# OPTIONS --sized-types #-}

module Haskell.Prim.Thunk where

open import Agda.Builtin.Size public

open import Haskell.Prim

record Thunk {ℓ} (a : @0 Size → Type ℓ) (@0 i : Size) : Type ℓ where
  constructor delay
  coinductive
  field force : {@0 j : Size< i} → a j
open Thunk public

{-# COMPILE AGDA2HS Thunk unboxed #-}
