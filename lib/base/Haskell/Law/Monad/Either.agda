module Haskell.Law.Monad.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Either

instance
  iPreLawfulMonadEither : PreLawfulMonad (Either a)
  iPreLawfulMonadEither = λ where
    .leftIdentity _ _ → refl
    .rightIdentity (Left  x) → refl
    .rightIdentity (Right x) → refl
    .associativity (Left  x) _ _ → refl
    .associativity (Right x) _ _ → refl
    .def->>->>= _ _ → refl
    .def-pure-return _ → refl
    .def-fmap->>= _ → λ where
      (Left  x) → refl
      (Right x) → refl
    .def-<*>->>= → λ where
      (Left  _) _ → refl
      (Right _) (Left  _) → refl
      (Right _) (Right _) → refl

  iIsLawfulMonadEither : IsLawfulMonad (Either a)
  iIsLawfulMonadEither = record {}
