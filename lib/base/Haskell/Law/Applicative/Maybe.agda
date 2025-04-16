module Haskell.Law.Applicative.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Applicative

open import Haskell.Law.Applicative.Def

open import Haskell.Law.Functor.Maybe

instance
  iLawfulApplicativeMaybe : IsLawfulApplicative Maybe
  iLawfulApplicativeMaybe .identity = λ { Nothing → refl; (Just _) → refl }

  iLawfulApplicativeMaybe .composition =
    λ { Nothing  _        _        → refl
      ; (Just _) Nothing  _        → refl
      ; (Just _) (Just _) Nothing  → refl
      ; (Just _) (Just _) (Just _) → refl
      }

  iLawfulApplicativeMaybe .homomorphism _ _ = refl

  iLawfulApplicativeMaybe .interchange = λ { Nothing _ → refl; (Just _) _ → refl }

  iLawfulApplicativeMaybe .functor = λ { _ Nothing → refl; _ (Just _) → refl }
