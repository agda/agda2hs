
module Haskell.Prim.Bounded where

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

record Bounded (a : Set) : Set where
  field
    minBound : a
    maxBound : a

open Bounded ⦃ ... ⦄ public

instance
  iBoundedWord : Bounded Word
  iBoundedWord .minBound = 0
  iBoundedWord .maxBound = 18446744073709551615

  iBoundedInt : Bounded Int
  iBoundedInt .minBound = -9223372036854775808
  iBoundedInt .maxBound = 9223372036854775807

  iBoundedBool : Bounded Bool
  iBoundedBool .minBound = false
  iBoundedBool .maxBound = true

  iBoundedChar : Bounded Char
  iBoundedChar .minBound = '\0'
  iBoundedChar .maxBound = '\1114111'

  iBoundedTuple₀ : Bounded (Tuple [])
  iBoundedTuple₀ .minBound = []
  iBoundedTuple₀ .maxBound = []

  iBoundedTuple : ∀ {as} → ⦃ Bounded a ⦄ → ⦃ Bounded (Tuple as) ⦄ → Bounded (Tuple (a ∷ as))
  iBoundedTuple .minBound = minBound ∷ minBound
  iBoundedTuple .maxBound = maxBound ∷ maxBound

  iBoundedOrdering : Bounded Ordering
  iBoundedOrdering .minBound = LT
  iBoundedOrdering .maxBound = GT

-- Sanity checks

private
  _ : addWord maxBound 1 ≡ minBound
  _ = refl

  _ : addInt maxBound 1 ≡ minBound
  _ = refl
