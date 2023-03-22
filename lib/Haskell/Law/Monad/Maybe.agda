module Haskell.Law.Monad.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Maybe

instance
  iLawfulMonadMaybe : IsLawfulMonad Maybe
  iLawfulMonadMaybe .leftIdentity a k = refl

  iLawfulMonadMaybe .rightIdentity Nothing  = refl
  iLawfulMonadMaybe .rightIdentity (Just _) = refl

  iLawfulMonadMaybe .associativity Nothing  _ _ = refl
  iLawfulMonadMaybe .associativity (Just _) _ _ = refl
