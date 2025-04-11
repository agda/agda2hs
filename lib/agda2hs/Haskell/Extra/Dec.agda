module Haskell.Extra.Dec where

open import Haskell.Prelude
open import Haskell.Extra.Refinement
open import Agda.Primitive

private variable
  ℓ : Level
  P : Type

@0 Reflects : Type ℓ → Bool → Type ℓ
Reflects P True  = P
Reflects P False = P → ⊥

of : {b : Bool} → if b then P else (P → ⊥) → Reflects P b
of {b = False} np = np
of {b = True}  p  = p

invert : ∀ {b} → Reflects P b → if b then P else (P → ⊥)
invert {b = False} np = np
invert {b = True}  p  = p

extractTrue : ∀ { b } → ⦃ true : b ≡ True ⦄ → Reflects P b → P
extractTrue {b = True} p = p

extractFalse : ∀ { b } → ⦃ true : b ≡ False ⦄ → Reflects P b → (P → ⊥)
extractFalse {b = False} np = np

mapReflects : ∀ {cond} → (a → b) → (b → a)
            → Reflects a cond → Reflects b cond
mapReflects {cond = False} f g x = x ∘ g
mapReflects {cond = True}  f g x = f x

Dec : ∀ {ℓ} → @0 Type ℓ → Type ℓ
Dec P = ∃ Bool (Reflects P)
{-# COMPILE AGDA2HS Dec inline #-}

mapDec : {@0 a b : Type}
       → @0 (a → b)
       → @0 (b → a)
       → Dec a → Dec b
mapDec f g (True  ⟨ x ⟩) = True  ⟨ f x   ⟩
mapDec f g (False ⟨ h ⟩) = False ⟨ h ∘ g ⟩
{-# COMPILE AGDA2HS mapDec transparent #-}

ifDec : Dec a → (@0 {{a}} → b) → (@0 {{a → ⊥}} → b) → b
ifDec (b ⟨ p ⟩) x y = if b then (λ where {{refl}} → x {{p}}) else (λ where {{refl}} → y {{p}})
{-# COMPILE AGDA2HS ifDec inline #-}

instance
  iDecIsTrue : {b : Bool} → Dec (IsTrue b)
  iDecIsTrue {False} = False ⟨ (λ ()) ⟩
  iDecIsTrue {True}  = True  ⟨ IsTrue.itsTrue ⟩
  {-# COMPILE AGDA2HS iDecIsTrue transparent #-}

  iDecIsFalse : {b : Bool} → Dec (IsFalse b)
  iDecIsFalse {b} = mapDec isTrueNotIsFalse isFalseIsTrueNot (iDecIsTrue {not b})
    where
      @0 isTrueNotIsFalse : {b : Bool} → IsTrue (not b) → IsFalse b
      isTrueNotIsFalse {False} IsTrue.itsTrue = IsFalse.itsFalse

      @0 isFalseIsTrueNot : {b : Bool} → IsFalse b → IsTrue (not b)
      isFalseIsTrueNot {False} IsFalse.itsFalse = IsTrue.itsTrue
  {-# COMPILE AGDA2HS iDecIsFalse inline #-}

