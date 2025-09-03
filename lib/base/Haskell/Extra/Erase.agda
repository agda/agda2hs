module Haskell.Extra.Erase where

  open import Agda.Primitive
  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Equality

  open import Haskell.Prim
  open import Haskell.Prim.List
  open import Haskell.Extra.Refinement
  open import Haskell.Law.Equality

  private variable
    @0 x y : a
    @0 xs  : List a

  record Erase (@0 a : Type ℓ) : Type ℓ where
    instance constructor iErased
    field @0 {{get}} : a
  open Erase public
  {-# COMPILE AGDA2HS Erase tuple #-}

  pattern Erased x = iErased {{x}}

  infixr 4 ⟨_⟩_
  record Σ0 (@0 a : Type) (b : @0 a → Type) : Type where
    constructor ⟨_⟩_
    field
      @0 proj₁ : a
      proj₂ : b proj₁
  open Σ0 public
  {-# COMPILE AGDA2HS Σ0 unboxed #-}

  pattern <_> x = record { proj₁ = _ ; proj₂ = x }

  -- Resurrection of erased values
  Singleton : (@0 x : a) → Type
  Singleton x = ∃ _ (x ≡_)

  {-# COMPILE AGDA2HS Singleton inline #-}

  pattern sing x = x ⟨ refl ⟩

  instance
    sing-id : {x : a} → Singleton x
    sing-id = sing _
  {-# COMPILE AGDA2HS sing-id inline #-}

  singCong : {@0 a : Type} {@0 x : a} (f : a → b) → Singleton x → Singleton (f x)
  singCong f (x ⟨ p ⟩) = f x ⟨ cong f p ⟩
  {-# COMPILE AGDA2HS singCong inline #-}

  singCong2 : (f : a → b → c) → Singleton x → Singleton y → Singleton (f x y)
  singCong2 f (x ⟨ p ⟩) (y ⟨ q ⟩) = f x y ⟨ cong₂ f p q ⟩
  {-# COMPILE AGDA2HS singCong2 inline #-}

  singHead : Singleton (x ∷ xs) → Singleton x
  singHead {x = x} (ys ⟨ p ⟩) =
    head ys
    ⟨ subst (λ ys → ⦃ @0 _ : NonEmpty ys ⦄ → x ≡ head ys)
            p refl ⟩
    where instance @0 ne : NonEmpty ys
                   ne = subst NonEmpty p itsNonEmpty
  {-# COMPILE AGDA2HS singHead inline #-}

  singTail : Singleton (x ∷ xs) → Singleton xs
  singTail {xs = xs} (ys ⟨ p ⟩) =
    tail ys
    ⟨ subst (λ ys → ⦃ @0 _ : NonEmpty ys ⦄ → xs ≡ tail ys)
            p refl ⟩
    where instance @0 ne : NonEmpty ys
                   ne = subst NonEmpty p itsNonEmpty
  {-# COMPILE AGDA2HS singTail inline #-}

  singErase : {@0 a : Type} {@0 x : a} → Singleton (Erased x)
  singErase {x = x} = Erased x ⟨ refl ⟩
  {-# COMPILE AGDA2HS singErase inline #-}

  erase-injective : Erased x ≡ Erased y → x ≡ y
  erase-injective refl = refl

  inspect_by_ : (x : a) → (Singleton x → b) → b
  inspect x by f = f (sing x)
