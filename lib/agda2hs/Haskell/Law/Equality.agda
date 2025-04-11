module Haskell.Law.Equality where

open import Haskell.Prim

open import Agda.Builtin.TrustMe

_≠_ : {A : Type} → A → A → Type
_≠_ a b = a ≡ b → ⊥

infix 4 _≠_

--------------------------------------------------
-- Basic Laws

cong : {A B : Type} → ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ (f : a → b → c) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

sym : ∀ {A : Type} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

subst : ∀ {A : Type} (P : A → Type) {x y : A} → x ≡ y → P x → P y
subst P refl z = z

--------------------------------------------------
-- Scary Things

trustMe : ∀ {a} {A : Type a} {x y : A} → x ≡ y
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


-------------------------------------------------
-- Utility Functions

subst0 : {@0 a : Type} (@0 p : @0 a → Type) {@0 x y : a} → @0 x ≡ y → p x → p y
subst0 p refl z = z
{-# COMPILE AGDA2HS subst0 transparent #-}
