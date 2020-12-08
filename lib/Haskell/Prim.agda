
-- Basic things needed by other primitive modules.

module Haskell.Prim where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.FromNat
open import Agda.Builtin.Equality

private
  variable
    ℓ : Level
    a b c d : Set


--------------------------------------------------
-- Booleans

infix -2 if_then_else_

if_then_else_ : {a : Set ℓ} → Bool → a → a → a
if false then x else y = y
if true  then x else y = x


--------------------------------------------------
-- Numbers

instance
  iNumberNat : Number Nat
  iNumberNat .Number.Constraint _ = ⊤
  iNumberNat .fromNat n = n


--------------------------------------------------
-- Lists

lengthNat : List a → Nat
lengthNat []       = 0
lengthNat (_ ∷ xs) = 1 + lengthNat xs


--------------------------------------------------
-- Proof things

data ⊥ : Set where

-- Use to bundle up constraints
data All {a b} {A : Set a} (B : A → Set b) : List A → Set (a ⊔ b) where
  instance
    allNil  : All B []
    allCons : ∀ {x xs} ⦃ i : B x ⦄ ⦃ is : All B xs ⦄ → All B (x ∷ xs)

data IsTrue : Bool → Set where
  instance itsTrue : IsTrue true

data IsFalse : Bool → Set where
  instance itsFalse : IsFalse false

data NonEmpty {a : Set} : List a → Set where
  instance itsNonEmpty : ∀ {x xs} → NonEmpty (x ∷ xs)

data TypeError (err : String) : Set where
