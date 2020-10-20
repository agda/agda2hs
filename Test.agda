
module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  a b : Set

{-# FOREIGN AGDA2HS
  import Prelude hiding (map, sum)
 #-}

data Exp (v : Set) : Set where
  Plus : Exp v → Exp v → Exp v
  Int : Nat → Exp v
  Var : v → Exp v

{-# COMPILE AGDA2HS Exp #-}

eval : (a → Nat) → Exp a → Nat
eval env (Plus a b) = eval env a + eval env b
eval env (Int n) = n
eval env (Var x) = env x

{-# COMPILE AGDA2HS eval #-}

sum : List Nat → Nat
sum []       = 0
sum (x ∷ xs) = x + sum xs

{-# COMPILE AGDA2HS sum #-}

{-# FOREIGN AGDA2HS -- comment #-}

append : List a → List a → List a
append []       ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

{-# COMPILE AGDA2HS append #-}

map : (a → b) → List a → List b
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

{-# COMPILE AGDA2HS map #-}

assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
assoc zero    b c = refl
assoc (suc a) b c rewrite assoc a b c = refl

thm : ∀ xs ys → sum (append xs ys) ≡ sum xs + sum ys
thm []       ys = refl
thm (x ∷ xs) ys rewrite thm xs ys | assoc x (sum xs) (sum ys) = refl

