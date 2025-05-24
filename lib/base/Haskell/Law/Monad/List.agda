module Haskell.Law.Monad.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def
open import Haskell.Law.List

open import Haskell.Law.Applicative.List

instance
  iPreLawfulMonadList : PreLawfulMonad List
  iPreLawfulMonadList .leftIdentity _ _ = ++-[] _

  iPreLawfulMonadList .rightIdentity [] = refl
  iPreLawfulMonadList .rightIdentity (x ∷ xs)
    rewrite iPreLawfulMonadList .PreLawfulMonad.rightIdentity xs
    = refl

  iPreLawfulMonadList .associativity []       f g = refl
  iPreLawfulMonadList .associativity (x ∷ xs) f g
    rewrite associativity xs f g
    | concatMap-++-distr (f x) (xs >>= f) g
    = refl

  iPreLawfulMonadList .def->>->>= _ _ = refl
  iPreLawfulMonadList .def-pure-return _ = refl

  iPreLawfulMonadList .def-fmap->>= _ [] = refl
  iPreLawfulMonadList .def-fmap->>= f (x ∷ xs)
    rewrite iPreLawfulMonadList .PreLawfulMonad.def-fmap->>= f xs
    = refl

  iPreLawfulMonadList .def-<*>->>= []       xs = refl
  iPreLawfulMonadList .def-<*>->>= (f ∷ fs) xs
    rewrite iPreLawfulMonadList .PreLawfulMonad.def-<*>->>= fs xs
    | map-concatMap f xs
    = refl

  iIsLawfulMonadList : IsLawfulMonad List
  iIsLawfulMonadList = record {}
