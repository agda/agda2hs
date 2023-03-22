module Haskell.Law.Semigroup.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Monoid

open import Haskell.Law.Equality
open import Haskell.Law.List
open import Haskell.Law.Semigroup.Def

instance
  iLawfulSemigroupList : IsLawfulSemigroup (List a)
  iLawfulSemigroupList .associativity []       _  _  = refl
  iLawfulSemigroupList .associativity (x ∷ xs) ys zs
    rewrite sym (++-assoc xs ys zs) 
    = refl