module Haskell.Law.Eq.Bool where

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality

instance
  iLawfulEqBool : IsLawfulEq Bool
  iLawfulEqBool .isEquality False False = ofY refl
  iLawfulEqBool .isEquality False True = ofN λ()
  iLawfulEqBool .isEquality True False = ofN λ()
  iLawfulEqBool .isEquality True True = ofY refl

