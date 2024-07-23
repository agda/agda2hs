module Haskell.Extra.Erase where

  open import Agda.Primitive
  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Equality

  open import Haskell.Prim
  open import Haskell.Prim.List
  open import Haskell.Law.Equality

  private variable
    @0 x y : a
    @0 xs  : List a

  record Erase (@0 a : Set ℓ) : Set ℓ where
    constructor Erased
    field @0 get : a
  open Erase public
  {-# COMPILE AGDA2HS Erase tuple #-}

  infixr 4 ⟨_⟩_
  record Σ0 (@0 a : Set) (b : @0 a → Set) : Set where
    constructor ⟨_⟩_
    field
      @0 proj₁ : a
      proj₂ : b proj₁
  open Σ0 public
  {-# COMPILE AGDA2HS Σ0 unboxed #-}

  pattern <_> x = record { proj₁ = _ ; proj₂ = x }

  -- Resurrection of erased values
  record Rezz (a : Set ℓ) (@0 x : a) : Set ℓ where
    constructor Rezzed
    field
      rezzed    : a
      @0 isRezz : rezzed ≡ x
  open Rezz public
  {-# COMPILE AGDA2HS Rezz unboxed #-}

  pattern rezz x = Rezzed x refl

  instance
    rezz-id : {x : a} → Rezz a x
    rezz-id = rezz _
  {-# COMPILE AGDA2HS rezz-id inline #-}

  rezzCong : {@0 a : Set} {@0 x : a} (f : a → b) → Rezz a x → Rezz b (f x)
  rezzCong f (Rezzed x p) = Rezzed (f x) (cong f p)
  {-# COMPILE AGDA2HS rezzCong inline #-}

  rezzCong2 : (f : a → b → c) → Rezz a x → Rezz b y → Rezz c (f x y)
  rezzCong2 f (Rezzed x p) (Rezzed y q) = Rezzed (f x y) (cong₂ f p q)
  {-# COMPILE AGDA2HS rezzCong2 inline #-}

  rezzHead : Rezz (List a) (x ∷ xs) → Rezz a x
  rezzHead {x = x} (Rezzed ys p) =
    Rezzed (head ys)
           (subst (λ ys → ⦃ @0 _ : NonEmpty ys ⦄ → head ys ≡ x)
              (sym p) refl)
    where instance @0 ne : NonEmpty ys
                   ne = subst NonEmpty (sym p) itsNonEmpty
  {-# COMPILE AGDA2HS rezzHead inline #-}

  rezzTail : Rezz (List a) (x ∷ xs) → Rezz (List a) xs
  rezzTail {xs = xs} (Rezzed ys p) =
    Rezzed (tail ys)
           (subst (λ ys → ⦃ @0 _ : NonEmpty ys ⦄ → tail ys ≡ xs)
              (sym p) refl)
    where instance @0 ne : NonEmpty ys
                   ne = subst NonEmpty (sym p) itsNonEmpty
  {-# COMPILE AGDA2HS rezzTail inline #-}

  rezzErase : {@0 a : Set} {@0 x : a} → Rezz (Erase a) (Erased x)
  rezzErase {x = x} = Rezzed (Erased x) refl
  {-# COMPILE AGDA2HS rezzErase inline #-}

  erase-injective : Erased x ≡ Erased y → x ≡ y
  erase-injective refl = refl

  inspect_by_ : (x : a) → (Rezz a x → b) → b
  inspect x by f = f (rezz x)
