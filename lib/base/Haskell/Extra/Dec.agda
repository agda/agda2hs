module Haskell.Extra.Dec where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple
open import Haskell.Extra.Refinement

open import Agda.Primitive

private variable
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

  iDecPair : {{Dec a}} → {{Dec b}} → Dec (a × b)
  iDecPair ⦃ b1 ⟨ r1 ⟩ ⦄ ⦃ b2 ⟨ r2 ⟩ ⦄ = (b1 && b2) ⟨ ×-reflects-&& r1 r2 ⟩
    where
      @0 ×-reflects-&& : ∀ {b1 b2 p q} → Reflects p b1 → Reflects q b2 → Reflects (p × q) (b1 && b2)
      ×-reflects-&& {False} {_}     r1 r2 = r1 ∘ fst
      ×-reflects-&& {True}  {False} r1 r2 = r2 ∘ snd
      ×-reflects-&& {True}  {True}  r1 r2 = r1 , r2
  {-# COMPILE AGDA2HS iDecPair inline #-}

  iDecEither : {{Dec a}} → {{Dec b}} → Dec (Either a b)
  iDecEither ⦃ b1 ⟨ r1 ⟩ ⦄ ⦃ b2 ⟨ r2 ⟩ ⦄ = (b1 || b2) ⟨ Either-reflects-|| r1 r2 ⟩
    where
      @0 Either-reflects-|| : ∀ {b1 b2 p q} → Reflects p b1 → Reflects q b2 → Reflects (Either p q) (b1 || b2)
      Either-reflects-|| {False} {False} r1 r2 = either r1 r2
      Either-reflects-|| {False} {True}  r1 r2 = Right r2
      Either-reflects-|| {True}  {_}     r1 r2 = Left r1
  {-# COMPILE AGDA2HS iDecEither inline #-}
