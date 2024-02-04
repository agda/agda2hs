module Haskell.Law.Eq.Int where

open import Haskell.Prim.Eq
open import Haskell.Prim.Int

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Word
open import Haskell.Law.Equality
open import Haskell.Law.Int

instance
  iLawfulEqInt : IsLawfulEq Int
  iLawfulEqInt .isEquality (int64 x) (int64 y) = mapReflects
    (cong int64) int64-injective (isEquality x y) 
