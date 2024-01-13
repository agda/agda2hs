module Haskell.Law.Eq.Nat where

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality
open import Haskell.Law.Nat

instance
  iLawfulEqNat : IsLawfulEq Nat
  iLawfulEqNat .isEquality zero    zero    = refl
  iLawfulEqNat .isEquality zero    (suc y) = λ ()
  iLawfulEqNat .isEquality (suc x) zero    = λ ()
  iLawfulEqNat .isEquality (suc x) (suc y) = mapReflects 
    (cong suc) 
    suc-injective 
    (isEquality x y)
