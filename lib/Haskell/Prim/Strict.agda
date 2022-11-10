
module Haskell.Prim.Strict where

open import Haskell.Prim

record Strict (a : Set ℓ) : Set ℓ where
  constructor !_
  field
    force : a
open Strict public

{-# COMPILE AGDA2HS Strict unboxed-strict #-}
