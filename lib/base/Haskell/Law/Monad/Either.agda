module Haskell.Law.Monad.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Either

instance
  iMonadLawsEither : MonadLaws (Either a)
  iMonadLawsEither .leftIdentity _ _ = refl
  iMonadLawsEither .rightIdentity (Left  x) = refl
  iMonadLawsEither .rightIdentity (Right x) = refl
  iMonadLawsEither .associativity (Left  x) = λ f g → refl
  iMonadLawsEither .associativity (Right x) = λ f g → refl

  iIsDefaultMonadEither : IsDefaultMonad (Either a)
  iIsDefaultMonadEither .def->>->>= = λ ma mb → refl
  iIsDefaultMonadEither .def-pure-return = λ x → refl
  iIsDefaultMonadEither .def-fmap->>= f (Left x) = refl
  iIsDefaultMonadEither .def-fmap->>= f (Right x) = refl
  iIsDefaultMonadEither .def-<*>->>= (Left x) = λ ma → refl
  iIsDefaultMonadEither .def-<*>->>= (Right x) (Left  y) = refl
  iIsDefaultMonadEither .def-<*>->>= (Right x) (Right y) = refl

  iIsLawfulMonadEither : IsLawfulMonad (Either a)
  iIsLawfulMonadEither = record {}
