module Haskell.Law.Semigroup.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Monoid

open import Haskell.Law.Equality
open import Haskell.Law.Semigroup.Def

instance
  iLawfulSemigroupEither : IsLawfulSemigroup (Either a b)
  iLawfulSemigroupEither .associativity (Left _)  _ _ = refl
  iLawfulSemigroupEither .associativity (Right _) _ _ = refl 