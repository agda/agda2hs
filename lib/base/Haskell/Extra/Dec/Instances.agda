module Haskell.Extra.Dec.Instances where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement

variable
  ℓ' : Level
  A : Set ℓ
  B : A → Set ℓ'
  x : A
  xs : List A
  p : Bool

instance
  decIsTrue : Dec (IsTrue p)
  decIsTrue {False} = False ⟨ (λ ()) ⟩
  decIsTrue {True} = True ⟨ IsTrue.itsTrue ⟩
  -- could specify transparent but this is incompatible with the instance search result
  {-# COMPILE AGDA2HS decIsTrue #-}

  decIsFalse : Dec (IsFalse p)
  decIsFalse {False} = True ⟨ IsFalse.itsFalse ⟩
  decIsFalse {True} = False ⟨ (λ ()) ⟩
  {-# COMPILE AGDA2HS decIsFalse #-}

  decNonEmpty : {xs : List a} → Dec (NonEmpty xs)
  decNonEmpty {xs = []} = False ⟨ (λ ()) ⟩
  decNonEmpty {xs = _ ∷ _} = True ⟨ NonEmpty.itsNonEmpty ⟩
  {-# COMPILE AGDA2HS decNonEmpty #-}

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

anyNone : (B x → ⊥) → (Any B xs → ⊥) → Any B (x ∷ xs) → ⊥
anyNone notHere _ anyHere = notHere it
anyNone _ notThere anyThere = notThere it

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
