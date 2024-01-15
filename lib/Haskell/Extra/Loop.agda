
open import Haskell.Prelude

module Haskell.Extra.Loop where

data Fuel (f : a → Either a b) : (x : Either a b) → Set where
  done : ∀ {y} → Fuel f (Right y)
  more : ∀ {x} → Fuel f (f x) → Fuel f (Left x)

tryFuel : (f : a → Either a b) (x : Either a b) (n : Nat) → Maybe (Fuel f x)
tryFuel f x         zero    = Nothing
tryFuel f (Left x)  (suc n) = more <$> tryFuel f (f x) n
tryFuel f (Right y) (suc n) = Just done

getFuel : (f : a → Either a b) (x : Either a b) (n : Nat)
        → {IsJust (tryFuel f x n)} → Fuel f x
getFuel f x n {p} = fromJust (tryFuel f x n) {p}

module _ {a b : Set} where
  loop : (f : a → Either a b) (x : a) → @0 Fuel f (Left x) → b
  loop f x (more n) = go (f x) n
    where
      go : (x : Either a b) → @0 Fuel f x → b
      go (Left x)  (more n) = go (f x) n
      go (Right y) done     = y
{-# COMPILE AGDA2HS loop #-}
