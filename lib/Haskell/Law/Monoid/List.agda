module Haskell.Law.Monoid.List where

open import Haskell.Prim
open import Haskell.Prim.Foldable
open import Haskell.Prim.List

open import Haskell.Prim.Monoid

open import Haskell.Law.Equality
open import Haskell.Law.List
open import Haskell.Law.Monoid.Def
open import Haskell.Law.Semigroup.Def
open import Haskell.Law.Semigroup.List

instance
  iLawfulMonoidList : IsLawfulMonoid (List a)
  iLawfulMonoidList .rightIdentity [] = refl
  iLawfulMonoidList .rightIdentity (x ∷ xs)
    rewrite ++-[] (x ∷ xs)
    = refl

  iLawfulMonoidList .leftIdentity [] = refl
  iLawfulMonoidList .leftIdentity (x ∷ xs)
    rewrite ++-[] (x ∷ xs)
    = refl

  iLawfulMonoidList .concatenation [] = refl
  iLawfulMonoidList .concatenation (x ∷ xs) 
    rewrite ++-[] (x ∷ xs)
      | concatenation xs
    = refl
