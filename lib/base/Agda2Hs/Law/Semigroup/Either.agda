module Agda2Hs.Law.Semigroup.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Monoid

open import Agda2Hs.Law.Equality
open import Agda2Hs.Law.Semigroup.Def

instance
  iLawfulSemigroupEither : IsLawfulSemigroup (Either a b)
  iLawfulSemigroupEither .associativity  = λ { (Left _) _ _ → refl; (Right _) _ _ → refl }
