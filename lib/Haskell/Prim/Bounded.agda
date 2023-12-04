
module Haskell.Prim.Bounded where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Int
open import Haskell.Prim.Maybe
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple
open import Haskell.Prim.Word

--------------------------------------------------
-- Bounded

record BoundedBelow (a : Set) : Set where
  field
    minBound : a

record BoundedAbove (a : Set) : Set where
  field
    maxBound : a

record Bounded (a : Set) : Set where
  field
    overlap ⦃ below ⦄ : BoundedBelow a
    overlap ⦃ above ⦄ : BoundedAbove a

{-# COMPILE AGDA2HS Bounded existing-class #-}

open BoundedBelow ⦃...⦄ public
open BoundedAbove ⦃...⦄ public

instance
  iBounded : ⦃ BoundedBelow a ⦄ → ⦃ BoundedAbove a ⦄ → Bounded a
  iBounded .Bounded.below = it
  iBounded .Bounded.above = it

instance
  iBoundedBelowNat : BoundedBelow Nat
  iBoundedBelowNat .minBound = 0

  iBoundedBelowWord : BoundedBelow Word
  iBoundedBelowWord .minBound = 0
  iBoundedAboveWord : BoundedAbove Word
  iBoundedAboveWord .maxBound = 18446744073709551615

  iBoundedBelowInt : BoundedBelow Int
  iBoundedBelowInt .minBound = -9223372036854775808
  iBoundedAboveInt : BoundedAbove Int
  iBoundedAboveInt .maxBound = 9223372036854775807

  iBoundedBelowBool : BoundedBelow Bool
  iBoundedBelowBool .minBound = False
  iBoundedAboveBool : BoundedAbove Bool
  iBoundedAboveBool .maxBound = True

  iBoundedBelowChar : BoundedBelow Char
  iBoundedBelowChar .minBound = '\0'
  iBoundedAboveChar : BoundedAbove Char
  iBoundedAboveChar .maxBound = '\1114111'

  iBoundedBelowUnit : BoundedBelow ⊤
  iBoundedBelowUnit .minBound = tt

  iBoundedAboveUnit : BoundedAbove ⊤
  iBoundedAboveUnit .maxBound = tt

  iBoundedBelowTuple₂ : ⦃ BoundedBelow a ⦄ → ⦃ BoundedBelow b ⦄
                      → BoundedBelow (a × b)
  iBoundedBelowTuple₂ .minBound = minBound , minBound
  iBoundedAboveTuple₂ : ⦃ BoundedAbove a ⦄ → ⦃ BoundedAbove b ⦄
                      → BoundedAbove (a × b)
  iBoundedAboveTuple₂ .maxBound = maxBound , maxBound

  iBoundedBelowTuple₃ : ⦃ BoundedBelow a ⦄ → ⦃ BoundedBelow b ⦄ → ⦃ BoundedBelow c ⦄
                      → BoundedBelow (a × b × c)
  iBoundedBelowTuple₃ .minBound = minBound , minBound , minBound
  iBoundedAboveTuple₃ : ⦃ BoundedAbove a ⦄ → ⦃ BoundedAbove b ⦄ → ⦃ BoundedAbove c ⦄
                      → BoundedAbove (a × b × c)
  iBoundedAboveTuple₃ .maxBound = maxBound , maxBound , maxBound

  iBoundedBelowOrdering : BoundedBelow Ordering
  iBoundedBelowOrdering .minBound = LT
  iBoundedAboveOrdering : BoundedAbove Ordering
  iBoundedAboveOrdering .maxBound = GT

-- Sanity checks

private
  _ : addWord maxBound 1 ≡ minBound
  _ = refl

  _ : addInt maxBound 1 ≡ minBound
  _ = refl
