module Haskell.Law.Applicative.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Applicative

open import Haskell.Law.Applicative.Def

instance
  iLawfulApplicativeMaybe : IsLawfulApplicative Maybe
  iLawfulApplicativeMaybe .identity Nothing  = refl
  iLawfulApplicativeMaybe .identity (Just _) = refl

  iLawfulApplicativeMaybe .composition Nothing  _        _        = refl
  iLawfulApplicativeMaybe .composition (Just _) Nothing  _        = refl
  iLawfulApplicativeMaybe .composition (Just _) (Just _) Nothing  = refl
  iLawfulApplicativeMaybe .composition (Just _) (Just _) (Just _) = refl

  iLawfulApplicativeMaybe .homomorphism _ _ = refl

  iLawfulApplicativeMaybe .interchange Nothing  _ = refl
  iLawfulApplicativeMaybe .interchange (Just _) _ = refl

  iLawfulApplicativeMaybe .functor _ Nothing  = refl
  iLawfulApplicativeMaybe .functor _ (Just _) = refl 