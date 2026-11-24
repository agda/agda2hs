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

data Delay (a : Type) (@0 i : Size) : Type where
  now : a → Delay a i
  later : Thunk (Delay a) i → Delay a i

bindDelay : Delay a i → (a → Delay b i) → Delay b i
bindDelay (now x)   f = f x
bindDelay (later x) f = later (λ where .force → bindDelay (x .force) f)

instance
  iFunctorDelay : ∀ {i} → Functor (λ a → Delay a i)
  iFunctorDelay {i} = record {DefaultFunctor iDefaultFunctorDelay}
    where
      iDefaultFunctorDelay : DefaultFunctor (λ a → Delay a i)
      iDefaultFunctorDelay .DefaultFunctor.fmap f m = bindDelay m (now ∘ f)

  iApplicativeDelay : ∀ {i} → Applicative (λ a → Delay a i)
  iApplicativeDelay {i} = record {DefaultApplicative iDefaultApplicativeDelay}
    where
      iDefaultApplicativeDelay : DefaultApplicative (λ a → Delay a i)
      iDefaultApplicativeDelay .DefaultApplicative.pure = now
      iDefaultApplicativeDelay .DefaultApplicative._<*>_ mf mx =
        bindDelay mf λ f → bindDelay mx λ x → now (f x)

  iMonadDelay : ∀ {i} → Monad (λ a → Delay a i)
  iMonadDelay {i} = record {DefaultMonad iDefaultMonadDelay}
    where
      iDefaultMonadDelay : DefaultMonad (λ a → Delay a i)
      iDefaultMonadDelay .DefaultMonad._>>=_ = bindDelay

data HasResult (x : a) : Delay a i → Type where
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
