module Haskell.Law.Eq.Def where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Integer
open import Haskell.Prim.Int
open import Haskell.Prim.Word
open import Haskell.Prim.Double
open import Haskell.Prim.Tuple
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either

open import Haskell.Prim.Eq

open import Haskell.Extra.Dec

open import Haskell.Law.Bool
open import Haskell.Law.Equality

record IsLawfulEq (e : Set) ⦃ iEq : Eq e ⦄ : Set₁ where
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

postulate instance
  iLawfulEqDouble : IsLawfulEq Double

  iLawfulEqChar : IsLawfulEq Char

  iLawfulEqTuple₂ : ⦃ iEqA : Eq a ⦄ ⦃ iEqB : Eq b ⦄
                  → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄
                  → IsLawfulEq (a × b)

  iLawfulEqTuple₃ : ⦃ iEqA : Eq a ⦄ ⦃ iEqB : Eq b ⦄ ⦃ iEqC : Eq c ⦄
                  → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄ → ⦃ IsLawfulEq c ⦄
                  → IsLawfulEq (a × b × c)

  iLawfulEqEither : ⦃ iEqA : Eq a ⦄ → ⦃ iEqB : Eq b ⦄ → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄ → Eq (Either a b)
