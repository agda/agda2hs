module Haskell.Law.Semigroup.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Monoid

open import Haskell.Law.Equality
open import Haskell.Law.Semigroup.Def

instance
  iLawfulSemigroupMaybe : ⦃ iSemA : Semigroup a ⦄ → ⦃ IsLawfulSemigroup a ⦄ → IsLawfulSemigroup (Maybe a)
  iLawfulSemigroupMaybe .associativity Nothing  _        _        = refl
  iLawfulSemigroupMaybe .associativity (Just _) Nothing  _        = refl
  iLawfulSemigroupMaybe .associativity (Just _) (Just _) Nothing  = refl
  iLawfulSemigroupMaybe .associativity (Just x) (Just y) (Just z)
    rewrite associativity x y z
    = refl
