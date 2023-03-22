module Haskell.Law.Monad.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Either

instance
  iLawfulMonadEither : IsLawfulMonad (Either a)
  iLawfulMonadEither .leftIdentity a k = refl

  iLawfulMonadEither .rightIdentity (Left _)  = refl
  iLawfulMonadEither .rightIdentity (Right _) = refl

  iLawfulMonadEither .associativity (Left _)  _ _ = refl
  iLawfulMonadEither .associativity (Right _) _ _ = refl
