module Haskell.Law.Monoid.Def where

open import Haskell.Prim
open import Haskell.Prim.Tuple

open import Haskell.Prim.Foldable
open import Haskell.Prim.Monoid

open import Haskell.Law.Semigroup.Def

record IsLawfulMonoid (a : Set) ⦃ iMonoidA : Monoid a ⦄ : Set₁ where
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

  iLawfulMonoidTuple₀ : IsLawfulMonoid (Tuple [])

  iLawfulMonoidTuple : ⦃ iSemA : Monoid a ⦄ → ⦃ iSemA : Monoid (Tuple as) ⦄
    → ⦃ IsLawfulMonoid a ⦄ → ⦃ IsLawfulMonoid (Tuple as) ⦄ 
    → IsLawfulMonoid (Tuple (a ∷ as))
 