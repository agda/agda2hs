module Haskell.Law.Functor.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Functor

open import Haskell.Law.Functor.Def

instance
  iLawfulFunctorEither : IsLawfulFunctor (Either a)
  iLawfulFunctorEither .identity (Left _)  = refl
  iLawfulFunctorEither .identity (Right _) = refl

  iLawfulFunctorEither .composition (Left _)  _ _ = refl
  iLawfulFunctorEither .composition (Right _) _ _ = refl
