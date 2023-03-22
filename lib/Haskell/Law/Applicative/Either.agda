module Haskell.Law.Applicative.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Applicative

open import Haskell.Law.Applicative.Def

open import Haskell.Law.Functor.Either

instance
  iLawfulApplicativeEither : IsLawfulApplicative (Either a)
  iLawfulApplicativeEither .identity (Left _)  = refl
  iLawfulApplicativeEither .identity (Right _) = refl

  iLawfulApplicativeEither .composition (Left _)  _         _         = refl
  iLawfulApplicativeEither .composition (Right _) (Left _)  _         = refl
  iLawfulApplicativeEither .composition (Right _) (Right _) (Left _)  = refl
  iLawfulApplicativeEither .composition (Right _) (Right _) (Right _) = refl

  iLawfulApplicativeEither .homomorphism _ _ = refl

  iLawfulApplicativeEither .interchange (Left _)  _ = refl
  iLawfulApplicativeEither .interchange (Right _) _ = refl

  iLawfulApplicativeEither .functor _ (Left _)  = refl
  iLawfulApplicativeEither .functor _ (Right _) = refl
