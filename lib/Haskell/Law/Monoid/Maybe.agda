module Haskell.Law.Monoid.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Monoid

open import Haskell.Law.Equality
open import Haskell.Law.Monoid.Def
open import Haskell.Law.Semigroup.Def
open import Haskell.Law.Semigroup.Maybe

instance
  iLawfulMonoidMaybe : ⦃ iMonoidA : Monoid a ⦄ → ⦃ iLawfulMonoidA : IsLawfulMonoid a ⦄ → IsLawfulMonoid (Maybe a)
  iLawfulMonoidMaybe .rightIdentity Nothing  = refl
  iLawfulMonoidMaybe .rightIdentity (Just _) = refl

  iLawfulMonoidMaybe .leftIdentity Nothing  = refl
  iLawfulMonoidMaybe .leftIdentity (Just _) = refl

  iLawfulMonoidMaybe .concatenation [] = refl
  iLawfulMonoidMaybe .concatenation (x ∷ xs) = trustMe -- TODO
  