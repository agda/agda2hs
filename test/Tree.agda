open import Haskell.Prim
open import Agda.Builtin.Nat

data _≤_ : Nat → Nat → Set where
  instance
    zero-≤ : ∀ {n} → zero ≤ n
    suc-≤ : ∀ {m n} → @0 {{m ≤ n}} → suc m ≤ suc n

data Tree {l u : Nat} : Set where
  Leaf  : @0 {{l ≤ u}} → Tree {l} {u}
  Node  : (x : Nat) → Tree {l} {x} → Tree {x} {u} → Tree {l} {u}
{-# COMPILE AGDA2HS Tree #-}
