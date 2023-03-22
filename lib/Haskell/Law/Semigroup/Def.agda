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

  iLawfulSemigroupTuple₀ : IsLawfulSemigroup (Tuple [])

  iLawfulSemigroupTuple : ⦃ iSemA : Semigroup a ⦄ → ⦃ iSemA : Semigroup (Tuple as) ⦄
    → ⦃ IsLawfulSemigroup a ⦄ → ⦃ IsLawfulSemigroup (Tuple as) ⦄ 
    → IsLawfulSemigroup (Tuple (a ∷ as))
 