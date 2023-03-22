module Haskell.Law.Monad.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.List
open import Haskell.Law.Equality

instance
  iLawfulMonadList : IsLawfulMonad List
  iLawfulMonadList .leftIdentity a k = trustMe

  iLawfulMonadList .rightIdentity [] = refl
  iLawfulMonadList .rightIdentity (x ∷ xs)
    rewrite rightIdentity xs
    = refl

  iLawfulMonadList .associativity [] f g = refl
  iLawfulMonadList .associativity (x ∷ xs) f g
    rewrite associativity xs f g
    = trustMe

    -- foldMapList g (f x) ++ foldMapList g (foldMapList f xs)
    -- ≡
    -- foldMapList g (f x ++ foldMapList f xs)
