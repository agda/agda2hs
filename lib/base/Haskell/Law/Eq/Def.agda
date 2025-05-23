module Haskell.Law.Eq.Def where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Double

open import Haskell.Prim.Eq

open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement

open import Haskell.Law.Bool
open import Haskell.Law.Equality

record IsLawfulEq (e : Type) ⦃ iEq : Eq e ⦄ : Type₁ where
  field
    isEquality : ∀ (x y : e) → Reflects (x ≡ y) (x == y)

  equality : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
  equality x y h = extractTrue ⦃ h ⦄ (isEquality x y)

  nequality : ∀ (x y : e) → (x == y) ≡ False → (x ≡ y → ⊥)
  nequality x y h = extractFalse ⦃ h ⦄ (isEquality x y)

  -- contrapositive of nequality
  equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True
  equality' x y h with x == y in eq
  ... | False = magic (nequality x y eq h)
  ... | True = refl

  -- contrapositive of equality
  nequality' : ∀ (x y : e) → (x ≡ y → ⊥) → (x == y) ≡ False
  nequality' x y h with x == y in eq
  ... | True = magic (h (equality x y eq))
  ... | False = refl

open IsLawfulEq ⦃ ... ⦄ public

-- Types with a lawful Eq instance have decidable equality
_≟_ : {{_ : Eq a}} {{_ : IsLawfulEq a}} → (x y : a) → Dec (x ≡ y)
x ≟ y = (x == y) ⟨ isEquality x y ⟩

{-# COMPILE AGDA2HS _≟_ inline #-}

-- Reflexivity: x == x = True
eqReflexivity : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
              → ∀ (x : e) → (x == x) ≡ True
eqReflexivity x = equality' x x refl

-- Symmetry: x == y = y == x
eqSymmetry : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
           → ∀ (x y : e) → (x == y) ≡ (y == x)
eqSymmetry x y with x == y in eq
... | True  = sym (equality' y x (sym (equality x y eq)))
... | False = sym (nequality' y x (λ qe → (nequality x y eq) (sym qe)))

-- Transitivity: if x == y && y == z = True, then x == z = True
eqTransitivity : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
               → ∀ (x y z : e) → ((x == y) && (y == z)) ≡ True → (x == z) ≡ True
eqTransitivity x y z h
  = equality' x z (trans
    (equality x y (&&-leftTrue (x == y) (y == z) h))
    (equality y z (&&-rightTrue (x == y) (y == z) h)))

-- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
eqExtensionality : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
                 → ⦃ iEq : Eq a ⦄ → ⦃ iLawfulEq : IsLawfulEq a ⦄
                 → ∀ ( x y : e ) ( f : e → a ) → (x == y) ≡ True → (f x == f y) ≡ True
eqExtensionality x y f h = equality' (f x) (f y) (cong f (equality x y h))

-- Negation: x /= y = not (x == y)
eqNegation : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
           → ∀ { x y : e } → (x /= y) ≡ not (x == y)
eqNegation = refl

