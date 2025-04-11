module Haskell.Law.Functor.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Functor

open import Haskell.Law.Functor.Def

instance
  iLawfulFunctorEither : IsLawfulFunctor (Either a)
  iLawfulFunctorEither .identity = λ { (Left _) → refl; (Right _) → refl }

  iLawfulFunctorEither .composition = λ { (Left _) _ _ → refl; (Right _) _ _ → refl }
