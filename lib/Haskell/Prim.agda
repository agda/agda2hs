{-# OPTIONS --no-auto-inline #-}

-- Basic things needed by other primitive modules.

module Haskell.Prim where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit       public
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Agda.Builtin.FromNat    public
open import Agda.Builtin.FromNeg    public
open import Agda.Builtin.FromString public

variable
  @0 ℓ : Level
  @0 a b c d e : Set
  @0 f m s t : Set → Set


--------------------------------------------------
-- Functions

id : a → a
id x = x

infixr 9 _∘_
_∘_ : (b → c) → (a → b) → a → c
(f ∘ g) x = f (g x)

flip : (a → b → c) → b → a → c
flip f x y = f y x

const : a → b → a
const x _ = x

infixr 0 _$_
_$_ : (a → b) → a → b
f $ x = f x


--------------------------------------------------
-- Language constructs

infix -1 case_of_
case_of_ : a → (a → b) → b
case x of f = f x

infix -2 if_then_else_
if_then_else_ : {@0 a : Set ℓ} → Bool → a → a → a
if false then x else y = y
if true  then x else y = x

--------------------------------------------------
-- Agda strings

instance
  iIsStringAgdaString : IsString String
  iIsStringAgdaString .IsString.Constraint _ = ⊤
  iIsStringAgdaString .fromString s = s


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

it : ∀ {@0 ℓ} {@0 a : Set ℓ} → ⦃ a ⦄ → a
it ⦃ x ⦄ = x
