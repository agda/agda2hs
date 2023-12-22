module Haskell.Law.Monad.List where

open import Haskell.Prim
open import Haskell.Prim.Foldable
open import Haskell.Prim.List
open import Haskell.Prim.Monoid

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def
open import Haskell.Law.List

open import Haskell.Law.Applicative.List
open import Haskell.Law.Equality

concatMap-distr : ∀ (xs ys : List a) (f : a → List b ) → 
  ((concatMap f xs) ++ (concatMap f ys)) ≡ (concatMap f (xs ++ ys))
concatMap-distr [] ys f = refl
concatMap-distr (x ∷ xs) ys f
  rewrite ++-assoc (f x) (concatMap f xs) (concatMap f ys)
  | concatMap-distr xs ys f
 = refl

instance
  iLawfulMonadList :  IsLawfulMonad List
  iLawfulMonadList .leftIdentity a k 
    rewrite ++-[] (k a)
    = refl

  iLawfulMonadList .rightIdentity [] = refl
  iLawfulMonadList .rightIdentity (_ ∷ xs)
    rewrite rightIdentity xs
    = refl

  iLawfulMonadList .associativity [] f g = refl
  iLawfulMonadList .associativity (x ∷ []) f g 
    rewrite ++-[] (concatMap g (f x))
     |  ++-[] (f x)
    = refl
  iLawfulMonadList .associativity (x ∷ xs) f g
    rewrite associativity xs f g
    | concatMap-distr (f x) (concatMap f xs) g
    = refl  

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
 