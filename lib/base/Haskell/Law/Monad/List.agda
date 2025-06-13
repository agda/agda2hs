module Haskell.Law.Monad.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def
open import Haskell.Law.List

open import Haskell.Law.Applicative.List

instance
  iMonadLawsList : MonadLaws List
  iMonadLawsList .leftIdentity _ _ = ++-[] _

  iMonadLawsList .rightIdentity [] = refl
  iMonadLawsList .rightIdentity (x ∷ xs)
    rewrite iMonadLawsList .MonadLaws.rightIdentity xs
    = refl

  iMonadLawsList .associativity []       f g = refl
  iMonadLawsList .associativity (x ∷ xs) f g
    rewrite associativity xs f g
    | concatMap-++-distr (f x) (xs >>= f) g
    = refl

  iIsDefaultMonadList : IsDefaultMonad List
  iIsDefaultMonadList .def->>->>= _ _ = refl
  iIsDefaultMonadList .def-pure-return _ = refl
  iIsDefaultMonadList .def-fmap->>= _ [] = refl
  iIsDefaultMonadList .def-fmap->>= f (x ∷ xs)
    rewrite iIsDefaultMonadList .IsDefaultMonad.def-fmap->>= f xs
    = refl
  iIsDefaultMonadList .def-<*>->>= []       xs = refl
  iIsDefaultMonadList .def-<*>->>= (f ∷ fs) xs
    rewrite iIsDefaultMonadList .IsDefaultMonad.def-<*>->>= fs xs
    | map-concatMap f xs
    = refl

  iIsLawfulMonadList : IsLawfulMonad List
  iIsLawfulMonadList = record {}
