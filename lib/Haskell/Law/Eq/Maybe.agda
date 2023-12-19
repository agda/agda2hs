module Haskell.Law.Eq.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Maybe

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality
open import Haskell.Law.Maybe

instance
  iLawfulEqMaybe : ⦃ iEqA : Eq a ⦄ → ⦃ IsLawfulEq a ⦄ → IsLawfulEq (Maybe a)
  iLawfulEqMaybe .isEquality Nothing Nothing = refl
  iLawfulEqMaybe .isEquality Nothing (Just _) = λ()
  iLawfulEqMaybe .isEquality (Just _) Nothing = λ()
  iLawfulEqMaybe .isEquality (Just x) (Just y) = mapReflects (cong Just) injective (isEquality x y)

