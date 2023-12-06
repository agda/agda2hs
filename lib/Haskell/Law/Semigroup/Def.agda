module Haskell.Law.Semigroup.Def where

open import Haskell.Prim
open import Haskell.Prim.Tuple

open import Haskell.Prim.Monoid

record IsLawfulSemigroup (a : Set) ⦃ iSemigroupA : Semigroup a ⦄ : Set₁ where
  field
    -- Associativity: x <> (y <> z) = (x <> y) <> z
    associativity : (x y z : a) → x <> (y <> z) ≡ (x <> y) <> z

open IsLawfulSemigroup ⦃ ... ⦄ public

postulate instance
  iLawfulSemigroupFun : ⦃ iSemB : Semigroup b ⦄ → ⦃ IsLawfulSemigroup b ⦄ → IsLawfulSemigroup (a → b)

  iLawfulSemigroupUnit : IsLawfulSemigroup ⊤

  iLawfulSemigroupTuple₂ : ⦃ iSemA : Semigroup a ⦄ ⦃ iSemB : Semigroup b ⦄
                         → ⦃ IsLawfulSemigroup a ⦄ → ⦃ IsLawfulSemigroup b ⦄
                         → IsLawfulSemigroup (a × b)

  iLawfulSemigroupTuple₃ : ⦃ iSemA : Semigroup a ⦄ ⦃ iSemB : Semigroup b ⦄ ⦃ iSemC : Semigroup c ⦄
                         → ⦃ IsLawfulSemigroup a ⦄ → ⦃ IsLawfulSemigroup b ⦄ → ⦃ IsLawfulSemigroup c ⦄
                         → IsLawfulSemigroup (a × b × c)

