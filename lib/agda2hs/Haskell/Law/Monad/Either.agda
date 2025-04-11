module Haskell.Law.Monad.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Either

instance
  iLawfulMonadEither : IsLawfulMonad (Either a)
  iLawfulMonadEither .leftIdentity _ _ = refl

  iLawfulMonadEither .rightIdentity = λ { (Left _) → refl; (Right _) → refl }

  iLawfulMonadEither .associativity = λ { (Left _) _ _ → refl; (Right _) _ _ → refl }

  iLawfulMonadEither .pureIsReturn _ = refl

  iLawfulMonadEither .sequence2bind =
    λ { (Left _)  _         → refl
      ; (Right _) (Left _)  → refl
      ; (Right _) (Right _) → refl
      }

  iLawfulMonadEither .fmap2bind = λ { _ (Left _) → refl; _ (Right _) → refl }

  iLawfulMonadEither .rSequence2rBind =
    λ { (Left _)  _         → refl
      ; (Right _) (Left _)  → refl
      ; (Right _) (Right _) → refl
      }
