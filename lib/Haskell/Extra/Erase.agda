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
  Rezz : (@0 x : a) → Type
  Rezz x = ∃ _ (x ≡_)

  {-# COMPILE AGDA2HS Rezz inline #-}

  pattern rezz x = x ⟨ refl ⟩

  instance
    rezz-id : {x : a} → Rezz x
    rezz-id = rezz _
  {-# COMPILE AGDA2HS rezz-id inline #-}

  rezzCong : {@0 a : Type} {@0 x : a} (f : a → b) → Rezz x → Rezz (f x)
  rezzCong f (x ⟨ p ⟩) = f x ⟨ cong f p ⟩
  {-# COMPILE AGDA2HS rezzCong inline #-}

  rezzCong2 : (f : a → b → c) → Rezz x → Rezz y → Rezz (f x y)
  rezzCong2 f (x ⟨ p ⟩) (y ⟨ q ⟩) = f x y ⟨ cong₂ f p q ⟩
  {-# COMPILE AGDA2HS rezzCong2 inline #-}

  rezzHead : Rezz (x ∷ xs) → Rezz x
  rezzHead {x = x} (ys ⟨ p ⟩) =
    head ys
    ⟨ subst (λ ys → ⦃ @0 _ : NonEmpty ys ⦄ → x ≡ head ys)
            p refl ⟩
    where instance @0 ne : NonEmpty ys
                   ne = subst NonEmpty p itsNonEmpty
  {-# COMPILE AGDA2HS rezzHead inline #-}

  rezzTail : Rezz (x ∷ xs) → Rezz xs
  rezzTail {xs = xs} (ys ⟨ p ⟩) =
    tail ys
    ⟨ subst (λ ys → ⦃ @0 _ : NonEmpty ys ⦄ → xs ≡ tail ys)
            p refl ⟩
    where instance @0 ne : NonEmpty ys
                   ne = subst NonEmpty p itsNonEmpty
  {-# COMPILE AGDA2HS rezzTail inline #-}

  rezzErase : {@0 a : Type} {@0 x : a} → Rezz (Erased x)
  rezzErase {x = x} = Erased x ⟨ refl ⟩
  {-# COMPILE AGDA2HS rezzErase inline #-}

  erase-injective : Erased x ≡ Erased y → x ≡ y
  erase-injective refl = refl

  inspect_by_ : (x : a) → (Rezz x → b) → b
  inspect x by f = f (rezz x)
