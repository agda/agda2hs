{-# OPTIONS --sized-types #-}

module Haskell.Extra.Delay where

open import Agda.Builtin.Size public

open import Haskell.Prelude

open import Haskell.Data.Maybe
open import Haskell.Extra.Refinement
open import Haskell.Prim.Thunk

private variable
  x y z : a
  @0 i : Size

data Delay (a : Set) (@0 i : Size) : Set where
  now : a → Delay a i
  later : Thunk (Delay a) i → Delay a i

data HasResult (x : a) : Delay a i → Set where
  now   : HasResult x (now x)
  later : HasResult x (y .force) → HasResult x (later y)

runDelay : {@0 x : a} (y : Delay a ∞) → @0 HasResult x y → a
runDelay (now x) now = x
runDelay (later y) (later p) = runDelay (y .force) p

runDelaySound : {@0 x : a} (y : Delay a ∞) → (@0 hr : HasResult x y) → runDelay y hr ≡ x
runDelaySound (now x) now = refl
runDelaySound (later y) (later hr) = runDelaySound (y .force) hr

-- tryDelay and unDelay cannot and should not be compiled to Haskell,
-- so they are marked as erased.
@0 tryDelay : (y : Delay a ∞) → Nat → Maybe (∃ a (λ x → HasResult x y))
tryDelay (now x)   _       = Just (x ⟨ now ⟩)
tryDelay (later y) zero    = Nothing
tryDelay (later y) (suc n) = fmap (mapRefine later) (tryDelay (y .force) n)

@0 unDelay : (y : Delay a ∞) (n : Nat) → @0 {IsJust (tryDelay y n)} → a
unDelay y n {p} = fromJust (tryDelay y n) {p} .value
