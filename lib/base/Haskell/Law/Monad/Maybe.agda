module Haskell.Law.Monad.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.Maybe

instance
  iMonadLawsMaybe : MonadLaws Maybe
  iMonadLawsMaybe .leftIdentity _ _ = refl
  iMonadLawsMaybe .rightIdentity Nothing  = refl
  iMonadLawsMaybe .rightIdentity (Just x) = refl
  iMonadLawsMaybe .associativity Nothing  = λ f g → refl
  iMonadLawsMaybe .associativity (Just x) = λ f g → refl

  iIsDefaultMonadMaybe : IsDefaultMonad Maybe
  iIsDefaultMonadMaybe .def->>->>= = λ ma mb → refl
  iIsDefaultMonadMaybe .def-pure-return = λ x → refl
  iIsDefaultMonadMaybe .def-fmap->>= f Nothing  = refl
  iIsDefaultMonadMaybe .def-fmap->>= f (Just x) = refl
  iIsDefaultMonadMaybe .def-<*>->>= Nothing = λ ma → refl
  iIsDefaultMonadMaybe .def-<*>->>= (Just x) Nothing = refl
  iIsDefaultMonadMaybe .def-<*>->>= (Just x) (Just y) = refl

  iIsLawfulMonadMaybe : IsLawfulMonad Maybe
  iIsLawfulMonadMaybe = record {}
