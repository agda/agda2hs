module Haskell.Law.Monoid.Def where

open import Haskell.Prim
open import Haskell.Prim.Tuple

open import Haskell.Prim.Foldable
open import Haskell.Prim.Monoid

open import Haskell.Law.Semigroup.Def

record IsLawfulMonoid (a : Type) ⦃ iMonoidA : Monoid a ⦄ : Type₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulSemigroup a

    -- Right identity: x <> mempty = x
    rightIdentity : (x : a) → x <> mempty ≡ x

    -- Left identity: mempty <> x = x
    leftIdentity : (x : a) → mempty <> x ≡ x

    -- Concatenation: mconcat = foldr (<>) mempty
    concatenation : (xs : List a) → mconcat xs ≡ foldr _<>_ mempty xs

open IsLawfulMonoid ⦃ ... ⦄ public

postulate instance
  iLawfulMonoidFun : ⦃ iSemB : Monoid b ⦄ → ⦃ IsLawfulMonoid b ⦄ → IsLawfulMonoid (a → b)

  iLawfulMonoidUnit : IsLawfulMonoid ⊤

  iLawfulMonoidTuple₂ : ⦃ iSemA : Monoid a ⦄ ⦃ iSemB : Monoid b ⦄
                      → ⦃ IsLawfulMonoid a ⦄ → ⦃ IsLawfulMonoid b ⦄
                      → IsLawfulMonoid (a × b)

  iLawfulMonoidTuple₃ : ⦃ iSemA : Monoid a ⦄ ⦃ iSemB : Monoid b ⦄ ⦃ iSemC : Monoid c ⦄
                      → ⦃ IsLawfulMonoid a ⦄ → ⦃ IsLawfulMonoid b ⦄ → ⦃ IsLawfulMonoid c ⦄
                      → IsLawfulMonoid (a × b × c)

