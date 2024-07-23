module Haskell.Extra.Sigma where

record Σ (a : Set) (b : @0 a → Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b fst
open Σ public
{-# COMPILE AGDA2HS Σ tuple #-}

infix 2 Σ-syntax

Σ-syntax : (a : Set) → (@0 a → Set) → Set
Σ-syntax = Σ
{-# COMPILE AGDA2HS Σ-syntax inline #-}

syntax Σ-syntax a (λ x → b) = Σ[ x ∈ a ] b
