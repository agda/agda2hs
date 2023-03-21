module Haskell.Law.Functor.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Functor

open import Haskell.Law.Functor.Def

instance
  iLawfulFunctorMaybe : IsLawfulFunctor Maybe
  iLawfulFunctorMaybe .identity Nothing = refl
  iLawfulFunctorMaybe .identity (Just _) = refl

  iLawfulFunctorMaybe .composition Nothing  _ _ = refl
  iLawfulFunctorMaybe .composition (Just x) _ _ = refl
