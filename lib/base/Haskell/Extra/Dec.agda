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


  decNonEmpty : {xs : List a} → Dec (NonEmpty xs)
  decNonEmpty {xs = []} = False ⟨ (λ ()) ⟩
  decNonEmpty {xs = _ ∷ _} = True ⟨ NonEmpty.itsNonEmpty ⟩
  {-# COMPILE AGDA2HS decNonEmpty #-}

module _ where
  open import Haskell.Prim hiding (ℓ)
  variable
    ℓ' : Level
    A : Set ℓ
    B : A → Set ℓ'
    x : A
    xs : List A

  anyNone : (B x → ⊥) → (Any B xs → ⊥) → Any B (x ∷ xs) → ⊥
  anyNone notHere _ anyHere = notHere it
  anyNone _ notThere anyThere = notThere it

  allNoHead : (B x → ⊥) → All B (x ∷ xs) → ⊥
  allNoHead ni allCons = ni it

  allNoTail : (All B xs → ⊥) → All B (x ∷ xs) → ⊥
  allNoTail np allCons = np it

interleaved mutual
  instance
    -- must name these variables explicitly or Agda2Hs gets confused
    decAll : ∀ {a : Set ℓ} {B : a → Set ℓ'} {xs} ⦃ p : ∀ {x} → Dec (B x) ⦄ → Dec (All B xs)

  decAllTail : ∀ {a : Set ℓ} {B : a → Set ℓ'} {@0 x} {@0 xs} ⦃ @0 i : B x ⦄ → Dec (All B xs) → Dec (All B (x ∷ xs))
  decAllTail (False ⟨ p ⟩) = False ⟨ allNoTail p ⟩
  decAllTail (True ⟨ p ⟩) = True ⟨ allCons ⦃ is = p ⦄ ⟩

  decAllHead : ∀ {a : Set ℓ} {B : a → Set ℓ'} {@0 x} {xs} → ⦃ Dec (B x) ⦄ → ⦃ p : ∀ {x} → Dec (B x) ⦄ → Dec (All B (x ∷ xs))
  decAllHead ⦃ False ⟨ i ⟩ ⦄ = False ⟨ allNoHead i ⟩
  decAllHead ⦃ True ⟨ i ⟩ ⦄ = decAllTail ⦃ i = i ⦄ decAll

  decAll {xs = []} = True ⟨ allNil ⟩
  decAll {xs = x ∷ xs} = decAllHead

  {-# COMPILE AGDA2HS decAll #-}
  {-# COMPILE AGDA2HS decAllTail #-}
  {-# COMPILE AGDA2HS decAllHead #-}


interleaved mutual
  instance
    decAny : ∀ {a : Set ℓ} {B : a → Set ℓ'} {xs} ⦃ p : ∀ {x} → Dec (B x) ⦄ → Dec (Any B xs)

  decAnyTail : ∀ {a : Set ℓ} {B : a → Set ℓ'} {@0 x} {@0 xs} (@0 i : B x → ⊥) → Dec (Any B xs) → Dec (Any B (x ∷ xs))
  decAnyTail i (False ⟨ p ⟩) = False ⟨ anyNone i p ⟩
  decAnyTail _ (True ⟨ p ⟩) = True ⟨ anyThere ⦃ is = p ⦄ ⟩

  decAnyHead : ∀ {a : Set ℓ} {B : a → Set ℓ'} {@0 x} {xs} → ⦃ Dec (B x) ⦄ → ⦃ p : ∀ {x} → Dec (B x) ⦄ → Dec (Any B (x ∷ xs))
  decAnyHead ⦃ False ⟨ i ⟩ ⦄ = decAnyTail i decAny
  decAnyHead ⦃ True ⟨ i ⟩ ⦄ = True ⟨ anyHere ⦃ i = i ⦄ ⟩

  decAny {xs = []} = False ⟨ (λ ()) ⟩
  decAny {xs = x ∷ xs} = decAnyHead

  {-# COMPILE AGDA2HS decAny #-}
  {-# COMPILE AGDA2HS decAnyTail #-}
  {-# COMPILE AGDA2HS decAnyHead #-}
