module Haskell.Extra.Sigma where

open import Haskell.Prelude

record Σ (a : Type) (b : @0 a → Type) : Type where
  constructor _,_
  field
    fst : a
    snd : b fst
open Σ public
{-# COMPILE AGDA2HS Σ tuple #-}

infix 2 Σ-syntax

Σ-syntax : (a : Type) → (@0 a → Type) → Type
Σ-syntax = Σ
{-# COMPILE AGDA2HS Σ-syntax inline #-}

syntax Σ-syntax a (λ x → b) = Σ[ x ∈ a ] b
