module Haskell.Law.Monad.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Maybe

instance
  iLawfulMonadMaybe : IsLawfulMonad Maybe
  iLawfulMonadMaybe .leftIdentity _ _ = refl

  iLawfulMonadMaybe .rightIdentity = λ { Nothing → refl; (Just _) → refl }

  iLawfulMonadMaybe .associativity = λ { Nothing _ _ → refl; (Just _) _ _ → refl }

  iLawfulMonadMaybe .pureIsReturn _ = refl

  iLawfulMonadMaybe .sequence2bind =
    λ { Nothing  _        → refl
      ; (Just _) Nothing  → refl
      ; (Just _) (Just _) → refl
      }

  iLawfulMonadMaybe .fmap2bind = λ { _ Nothing → refl; _ (Just _) → refl }

  iLawfulMonadMaybe .rSequence2rBind =
    λ { Nothing  _        → refl
      ; (Just _) Nothing  → refl
      ; (Just _) (Just _) → refl
      }

