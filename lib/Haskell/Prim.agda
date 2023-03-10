{-# OPTIONS --no-auto-inline #-}

-- Basic things needed by other primitive modules.
-- Note that this module exports types and functions that should not
-- be used directly in Haskell definitions, so you probably want to
-- import Haskell.Prelude instead.

module Haskell.Prim where

open import Agda.Primitive          public
open import Agda.Builtin.Bool       public renaming (true to True; false to False)
open import Agda.Builtin.Int        public renaming (Int to Integer)
open import Agda.Builtin.Nat        public renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Agda.Builtin.Char       public
open import Agda.Builtin.Unit       public
open import Agda.Builtin.Equality   public
open import Agda.Builtin.FromString public
open import Agda.Builtin.FromNat    public
open import Agda.Builtin.FromNeg    public
open import Agda.Builtin.String     public renaming (String to AgdaString)
open import Agda.Builtin.Word       public renaming (primWord64ToNat to w2n; primWord64FromNat to n2w)
open import Agda.Builtin.Strict     public
open import Agda.Builtin.List       public

variable
  ℓ : Level
  a b c d e : Set
  f m s t : Set → Set


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
case_of_ : {@0 a b : Set ℓ} → (a' : a) → ((a'' : a) → @0 {{ a' ≡ a'' }} → b) → b
case x of f = f x

infix -2 if_then_else_
if_then_else_ : {@0 a : Set ℓ} → (flg : Bool) → (@0 {{ flg ≡ True }} → a) → (@0 {{ flg ≡ False }} → a) → a
if False then x else y = y
if True  then x else y = x

--------------------------------------------------
-- Agda strings

instance
  iIsStringAgdaString : IsString AgdaString
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
lengthNat (_ ∷ xs) = addNat 1 (lengthNat xs)


--------------------------------------------------
-- Proof things

data ⊥ : Set where

-- Use to bundle up constraints
data All {a b} {A : Set a} (B : A → Set b) : List A → Set (a ⊔ b) where
  instance
    allNil  : All B []
    allCons : ∀ {x xs} ⦃ i : B x ⦄ ⦃ is : All B xs ⦄ → All B (x ∷ xs)

data IsTrue : Bool → Set where
  instance itsTrue : IsTrue True

data IsFalse : Bool → Set where
  instance itsFalse : IsFalse False

data NonEmpty {a : Set} : List a → Set where
  instance itsNonEmpty : ∀ {x xs} → NonEmpty (x ∷ xs)

data TypeError (err : AgdaString) : Set where

it : ∀ {@0 ℓ} {@0 a : Set ℓ} → ⦃ a ⦄ → a
it ⦃ x ⦄ = x
