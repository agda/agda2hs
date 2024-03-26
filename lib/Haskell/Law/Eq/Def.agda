module Haskell.Law.Eq.Def where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Double

open import Haskell.Prim.Eq

open import Haskell.Extra.Dec

open import Haskell.Law.Bool
open import Haskell.Law.Equality

record IsLawfulEq (e : Set) ⦃ iEq : Eq e ⦄ : Set₁ where
  field
    isEquality : ∀ (x y : e) → Reflects (x ≡ y) (x == y)

  equality : ∀ {x y : e} → (x == y) ≡ True → x ≡ y
  equality { x } { y } h = extractTrue ⦃ h ⦄ (isEquality x y)

  nequality : ∀ {x y : e} → (x == y) ≡ False → (x ≡ y → ⊥)
  nequality { x } { y } h = extractFalse ⦃ h ⦄ (isEquality x y)

  -- contrapositive of nequality
  equality' : ∀ {x y : e} → x ≡ y → (x == y) ≡ True
  equality' { x } { y } h with x == y in eq
  ... | False = magic (nequality eq h)
  ... | True = refl

  -- contrapositive of equality
  nequality' : ∀ {x y : e} → (x ≡ y → ⊥) → (x == y) ≡ False
  nequality' { x } { y } h with x == y in eq
  ... | True = magic (h (equality eq))
  ... | False = refl

open IsLawfulEq ⦃ ... ⦄ public

-- Reflexivity: x == x = True
eqReflexivity : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
              → ∀ (x : e) → (x == x) ≡ True
eqReflexivity x = equality' refl

-- Symmetry: x == y = y == x
eqSymmetry : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
           → ∀ (x y : e) → (x == y) ≡ (y == x)
eqSymmetry x y with x == y in eq
... | True  = sym (equality' (sym (equality eq)))
... | False = sym (nequality' (λ qe → (nequality eq) (sym qe)))

-- Transitivity: if x == y && y == z = True, then x == z = True
eqTransitivity : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
               → ∀ (x y z : e) → ((x == y) && (y == z)) ≡ True → (x == z) ≡ True
eqTransitivity x y z h
  = equality' (trans
    (equality (&&-leftTrue h))
    (equality (&&-rightTrue h)))

-- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
eqExtensionality : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
                 → ⦃ iEq : Eq a ⦄ → ⦃ iLawfulEq : IsLawfulEq a ⦄
                 → ∀ ( x y : e ) ( f : e → a ) → (x == y) ≡ True → (f x == f y) ≡ True
eqExtensionality x y f h = equality' (cong f (equality h))

-- Negation: x /= y = not (x == y)
eqNegation : ⦃ iEq : Eq e ⦄ → ⦃ IsLawfulEq e ⦄
           → ∀ { x y : e } → (x /= y) ≡ not (x == y)
eqNegation = refl

