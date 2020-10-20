
module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  a b : Set

{-# FOREIGN AGDA2HS
  import Data.List
  import Prelude
 #-}

data Exp : Set where
  plus : Exp → Exp → Exp
  int : Nat → Exp

{-# COMPILE AGDA2HS Exp #-}

sum : List Nat → Nat
sum []       = 0
sum (x ∷ xs) = x + sum xs

{-# COMPILE AGDA2HS sum #-}

{-# FOREIGN AGDA2HS -- comment #-}

append : List a → List a → List a
append []       ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

{-# COMPILE AGDA2HS append #-}

assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
assoc zero    b c = refl
assoc (suc a) b c rewrite assoc a b c = refl

thm : ∀ xs ys → sum (append xs ys) ≡ sum xs + sum ys
thm []       ys = refl
thm (x ∷ xs) ys rewrite thm xs ys | assoc x (sum xs) (sum ys) = refl

