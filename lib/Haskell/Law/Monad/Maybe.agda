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

  iLawfulMonadMaybe .pureIsReturn _ = refl

  iLawfulMonadMaybe .sequence2bind Nothing  _        = refl
  iLawfulMonadMaybe .sequence2bind (Just _) Nothing  = refl
  iLawfulMonadMaybe .sequence2bind (Just _) (Just _) = refl

  iLawfulMonadMaybe .fmap2bind _ Nothing  = refl
  iLawfulMonadMaybe .fmap2bind _ (Just _) = refl

  iLawfulMonadMaybe .rSequence2rBind Nothing  _        = refl
  iLawfulMonadMaybe .rSequence2rBind (Just _) Nothing  = refl
  iLawfulMonadMaybe .rSequence2rBind (Just _) (Just _) = refl

