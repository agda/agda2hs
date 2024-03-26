module Haskell.Law.Bool where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Either

open import Haskell.Law.Equality

--------------------------------------------------
-- &&

&&-sym : ∀ {a b : Bool} → (a && b) ≡ (b && a)
&&-sym { False } { False } = refl
&&-sym { False } { True }  = refl
&&-sym { True }  { False } = refl
&&-sym { True }  { True }  = refl

&&-semantics : ∀ {a b : Bool} → a ≡ True → b ≡ True → (a && b) ≡ True
&&-semantics { True } { True } _ _ = refl

&&-leftAssoc : ∀ {a b c : Bool} → (a && b && c) ≡ True → ((a && b) && c) ≡ True
&&-leftAssoc { True } { True } { True } _ = refl

&&-leftAssoc' : ∀ {a b c : Bool} → (a && b && c) ≡ ((a && b) && c)
&&-leftAssoc' { False } { b } { c } = refl
&&-leftAssoc' { True }  { b } { c } = refl

&&-leftTrue : ∀ {a b : Bool} → (a && b) ≡ True → a ≡ True
&&-leftTrue { True } { True } _ = refl

&&-leftTrue' : ∀ {a b c : Bool} → a ≡ (b && c) → a ≡ True → c ≡ True
&&-leftTrue' { .True } { True } { True } _ refl = refl

&&-rightTrue : ∀ {a b : Bool} → (a && b) ≡ True → b ≡ True
&&-rightTrue { True } { True } _ = refl

&&-rightTrue' : ∀ {a b c : Bool} → a ≡ (b && c) → a ≡ True → b ≡ True
&&-rightTrue' { .True } { True } { True } _ refl = refl

&&-eitherFalse : ∀ {a b : Bool} → (a && b) ≡ False → Either (a ≡ False) (b ≡ False)
&&-eitherFalse {False} { b } refl = Left refl
&&-eitherFalse {True} { .False } refl = Right refl

--------------------------------------------------
-- ||

-- if a then True else b

||-excludedMiddle : ∀ {a b : Bool} → (a || not a) ≡ True
||-excludedMiddle { False } { _ } = refl
||-excludedMiddle { True }  { _ } = refl

||-leftTrue : ∀ {a b : Bool} → a ≡ True → (a || b) ≡ True
||-leftTrue { .True } { b } refl = refl

||-rightTrue : ∀ {a b : Bool} → b ≡ True → (a || b) ≡ True
||-rightTrue { False } { .True } refl = refl
||-rightTrue { True } {  .True } refl = refl

--------------------------------------------------
-- not

not-not : ∀ {a : Bool} → not (not a) ≡ a
not-not { False } = refl
not-not { True }  = refl

not-involution : ∀ {a b : Bool} → a ≡ not b → not a ≡ b
not-involution { .(not b) } { b } refl = not-not

--------------------------------------------------
-- if_then_else_

ifFlip : ∀ b {t e : a} → (if b then t else e) ≡ (if not b then e else t)
ifFlip False = refl
ifFlip True  = refl

ifTrueEqThen : ∀ (b : Bool) {thn els : a} → b ≡ True → (if b then thn else els) ≡ thn
ifTrueEqThen .True refl = refl

ifFalseEqElse : ∀ (b : Bool) {thn els : a} → b ≡ False → (if b then thn else els) ≡ els
ifFalseEqElse .False refl = refl
