module Haskell.Law.Monad.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Maybe

instance
  iPreLawfulMonadMaybe : PreLawfulMonad Maybe
  iPreLawfulMonadMaybe = λ where
    .leftIdentity _ _ → refl
    .rightIdentity → λ where
      Nothing  → refl
      (Just _) → refl
    .associativity → λ where
      Nothing  _ _ → refl
      (Just _) _ _ → refl

    .def->>->>= _ _ → refl
    .def-pure-return _ → refl

    .def-fmap->>= _ → λ where
      Nothing → refl
      (Just _) → refl
    .def-<*>->>= → λ where
      Nothing  _        → refl
      (Just _) Nothing  → refl
      (Just _) (Just _) → refl

  iIsLawfulMonadMaybe : IsLawfulMonad Maybe
  iIsLawfulMonadMaybe = record {}
