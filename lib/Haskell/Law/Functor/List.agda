{-# OPTIONS --no-termination-check #-}

module Haskell.Law.Functor.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Functor

open import Haskell.Law.Equality
open import Haskell.Law.Functor.Def

instance
  iLawfulFunctorList : IsLawfulFunctor List
  iLawfulFunctorList .identity [] = refl
  iLawfulFunctorList .identity (x ∷ xs) rewrite IsLawfulFunctor.identity iLawfulFunctorList xs = refl

  iLawfulFunctorList .composition [] _ _ = refl
  iLawfulFunctorList .composition (x ∷ xs) f g rewrite IsLawfulFunctor.composition iLawfulFunctorList xs f g = refl