module Haskell.Law.Equality where

open import Haskell.Prim

open import Agda.Builtin.TrustMe

_≠_ : {A : Set} → A → A → Set
_≠_ a b = a ≡ b → ⊥

infix 4 _≠_

--------------------------------------------------
-- Basic Laws

cong : {A B : Set} → ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ (f : a → b → c) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

--------------------------------------------------
-- Scary Things

trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
trustMe = primTrustMe

--------------------------------------------------
-- ≡-Reasoning

infix  1 begin_
infixr 2 _≡⟨⟩_ step-≡ step-≡˘
infix  3 _∎

begin_ : ∀{x y : a} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : ∀ (x {y} : a) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : ∀ (x {y z} : a) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

step-≡˘ : ∀ (x {y z} : a) → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

_∎ : ∀ (x : a) → x ≡ x
_∎ _ = refl

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

--------------------------------------------------
-- Reflects idiom

data Reflects {p} (P : Set p) : Bool → Set p where
  ofY : ( p :   P )      → Reflects P True
  ofN : ( np : (P → ⊥) ) → Reflects P False

private
  variable
    p : Level
    P : Set p

of : ∀ {b} → if b then P else (P → ⊥) → Reflects P b
of {b = False} np = ofN np
of {b = True }  p = ofY p

invert : ∀ {b} → Reflects P b → if b then P else (P → ⊥)
invert (ofY  p) = p
invert (ofN np) = np

extractTrue : ∀ { b } → ⦃ true : b ≡ True ⦄ → Reflects P b → P
extractTrue (ofY p) = p

extractFalse : ∀ { b } → ⦃ true : b ≡ False ⦄ → Reflects P b → (P → ⊥)
extractFalse (ofN np) = np
