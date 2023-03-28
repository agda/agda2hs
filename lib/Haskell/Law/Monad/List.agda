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
  iLawfulMonadList .rightIdentity (_ ∷ xs)
    rewrite rightIdentity xs
    = refl

  iLawfulMonadList .associativity [] f g = refl
  iLawfulMonadList .associativity (_ ∷ xs) f g
    rewrite associativity xs f g
    = trustMe

    -- foldMapList g (f x) ++ foldMapList g (foldMapList f xs)
    -- ≡
    -- foldMapList g (f x ++ foldMapList f xs)

  iLawfulMonadList .pureIsReturn _ = refl

  iLawfulMonadList .sequence2bind [] _ = refl
  iLawfulMonadList .sequence2bind (_ ∷ _) [] = refl
  iLawfulMonadList .sequence2bind (f ∷ fs) (x ∷ xs) = trustMe

  iLawfulMonadList .fmap2bind f [] = refl
  iLawfulMonadList .fmap2bind f (_ ∷ xs)
    rewrite fmap2bind f xs
    = refl

  iLawfulMonadList .rSequence2rBind [] mb = refl
  iLawfulMonadList .rSequence2rBind (x ∷ ma) mb = trustMe
