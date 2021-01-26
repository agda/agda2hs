
module Haskell.Prim.Bounded where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.List

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

open BoundedBelow ⦃ ... ⦄ public
open BoundedAbove ⦃ ... ⦄ public

mkBounded : ⦃ BoundedBelow a ⦄ → ⦃ BoundedAbove a ⦄ → Bounded a
mkBounded .Bounded.below = it
mkBounded .Bounded.above = it

instance
  iBoundedBelowNatural : BoundedBelow Nat
  iBoundedBelowNatural .minBound = 0

  iBoundedBelowWord : BoundedBelow Word
  iBoundedBelowWord .minBound = 0
  iBoundedAboveWord : BoundedAbove Word
  iBoundedAboveWord .maxBound = 18446744073709551615

  iBoundedWord : Bounded Word
  iBoundedWord = mkBounded

  iBoundedBelowInt : BoundedBelow Int
  iBoundedBelowInt .minBound = -9223372036854775808
  iBoundedAboveInt : BoundedAbove Int
  iBoundedAboveInt .maxBound = 9223372036854775807

  iBoundedInt : Bounded Int
  iBoundedInt = mkBounded

  iBoundedBelowBool : BoundedBelow Bool
  iBoundedBelowBool .minBound = false
  iBoundedAboveBool : BoundedAbove Bool
  iBoundedAboveBool .maxBound = true

  iBoundedBool : Bounded Bool
  iBoundedBool = mkBounded

  iBoundedBelowChar : BoundedBelow Char
  iBoundedBelowChar .minBound = '\0'
  iBoundedAboveChar : BoundedAbove Char
  iBoundedAboveChar .maxBound = '\1114111'

  iBoundedChar : Bounded Char
  iBoundedChar = mkBounded

  iBoundedBelowTuple₀ : BoundedBelow (Tuple [])
  iBoundedBelowTuple₀ .minBound = []
  iBoundedAboveTuple₀ : BoundedAbove (Tuple [])
  iBoundedAboveTuple₀ .maxBound = []

  iBoundedTuple₀ : Bounded (Tuple [])
  iBoundedTuple₀ = mkBounded

  iBoundedBelowTuple : ∀ {as} → ⦃ BoundedBelow a ⦄ → ⦃ BoundedBelow (Tuple as) ⦄ → BoundedBelow (Tuple (a ∷ as))
  iBoundedBelowTuple .minBound = minBound ∷ minBound
  iBoundedAboveTuple : ∀ {as} → ⦃ BoundedAbove a ⦄ → ⦃ BoundedAbove (Tuple as) ⦄ → BoundedAbove (Tuple (a ∷ as))
  iBoundedAboveTuple .maxBound = maxBound ∷ maxBound

  iBoundedTuple : ∀ {as} → ⦃ Bounded a ⦄ → ⦃ Bounded (Tuple as) ⦄ → Bounded (Tuple (a ∷ as))
  iBoundedTuple = mkBounded

  iBoundedBelowOrdering : BoundedBelow Ordering
  iBoundedBelowOrdering .minBound = LT
  iBoundedAboveOrdering : BoundedAbove Ordering
  iBoundedAboveOrdering .maxBound = GT

  iBoundedOrdering : Bounded Ordering
  iBoundedOrdering = mkBounded

-- Sanity checks

private
  _ : addWord maxBound 1 ≡ minBound
  _ = refl

  _ : addInt maxBound 1 ≡ minBound
  _ = refl
