open import Haskell.Prim
open import Agda.Builtin.Nat

data _≤_ : Nat → Nat → Set where
  instance
    zero-≤ : ∀ {@0 n} → zero ≤ n
    suc-≤ : ∀ {@0 m n} → @0 {{m ≤ n}} → suc m ≤ suc n

data Tree (@0 l u : Nat) : Set where
  Leaf  : @0 {{l ≤ u}} → Tree l u
  Node  : (x : Nat) → Tree l x → Tree x u → Tree l u
{-# COMPILE AGDA2HS Tree #-}
