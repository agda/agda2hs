module Haskell.Law.Applicative.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Applicative

open import Haskell.Law.Applicative.Def

open import Haskell.Law.Functor.Either

instance
  iLawfulApplicativeEither : IsLawfulApplicative (Either a)
  -- (λ { true → true ; false → false })

  iLawfulApplicativeEither .identity = λ { (Left _) → refl; (Right _) → refl }

  iLawfulApplicativeEither .composition =
    λ { (Left _)  _         _         → refl
      ; (Right _) (Left _)  _         → refl
      ; (Right _) (Right _) (Left _)  → refl
      ; (Right _) (Right _) (Right _) → refl
      }

  iLawfulApplicativeEither .homomorphism _ _ = refl

  iLawfulApplicativeEither .interchange = λ { (Left _) _ → refl; (Right _) _ → refl }

  iLawfulApplicativeEither .functor = λ { _ (Left _) → refl; _ (Right _) → refl }
