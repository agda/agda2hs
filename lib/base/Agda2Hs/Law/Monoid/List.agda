module Agda2Hs.Law.Monoid.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Monoid

open import Agda2Hs.Law.List
open import Agda2Hs.Law.Monoid.Def
open import Agda2Hs.Law.Semigroup.Def
open import Agda2Hs.Law.Semigroup.List

instance
  iLawfulMonoidList : IsLawfulMonoid (List a)
  iLawfulMonoidList .rightIdentity [] = refl
  iLawfulMonoidList .rightIdentity (x ∷ xs)
    rewrite ++-[] (x ∷ xs)
    = refl

  iLawfulMonoidList .leftIdentity [] = refl
  iLawfulMonoidList .leftIdentity (x ∷ xs) = refl

  iLawfulMonoidList .concatenation [] = refl
  iLawfulMonoidList .concatenation (x ∷ xs)
    rewrite concatenation xs
    = refl
