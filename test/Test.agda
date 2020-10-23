
module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  a b : Set

{-# FOREIGN AGDA2HS
{-# LANGUAGE LambdaCase #-}
#-}

{-# FOREIGN AGDA2HS
import Prelude hiding (map, sum, (++))
import Data.Monoid
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

{-# FOREIGN AGDA2HS
-- comment
-- another comment
bla :: Int -> Int
bla n = n * 4

{- multi
   line
   comment
-}
#-}

_++_ : List a → List a → List a
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

{-# COMPILE AGDA2HS _++_ #-}

map : (a → b) → List a → List b
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

{-# COMPILE AGDA2HS map #-}

plus3 : List Nat → List Nat
plus3 = map (λ n → n + 3)

{-# COMPILE AGDA2HS plus3 #-}

doubleLambda : Nat → Nat → Nat
doubleLambda = λ a b → a + 2 * b

{-# COMPILE AGDA2HS doubleLambda #-}

assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
assoc zero    b c = refl
assoc (suc a) b c rewrite assoc a b c = refl

thm : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys
thm []       ys = refl
thm (x ∷ xs) ys rewrite thm xs ys | assoc x (sum xs) (sum ys) = refl

-- Monoid instance

record Monoid (A : Set) : Set where
  field mempty  : A
        mappend : A → A → A

open Monoid {{...}} public

{-# COMPILE AGDA2HS Monoid class #-}

instance
  MonoidNat : Monoid Nat
  mempty  {{MonoidNat}}     = 0
  mappend {{MonoidNat}} i j = i + j

sumMon : ∀{a} → {{Monoid a}} → List a → a
sumMon []       = mempty
sumMon (x ∷ xs) = mappend x (sumMon xs)

{-# COMPILE AGDA2HS sumMon #-}
