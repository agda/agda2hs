module Haskell.Law.Eq.Integer where

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality
open import Haskell.Law.Eq.Nat
open import Haskell.Law.Integer

instance
  iLawfulEqInteger : IsLawfulEq Integer
  iLawfulEqInteger .isEquality (pos n)    (pos m)    = mapReflects 
    (cong pos) pos-injective (isEquality n m)
  iLawfulEqInteger .isEquality (pos n)    (negsuc m) = λ () 
  iLawfulEqInteger .isEquality (negsuc n) (pos m)    = λ ()
  iLawfulEqInteger .isEquality (negsuc n) (negsuc m) = mapReflects 
    (cong negsuc) neg-injective (isEquality n m)
