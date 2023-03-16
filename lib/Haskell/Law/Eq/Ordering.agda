module Haskell.Law.Eq.Ordering where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord using ( Ordering; LT; GT; EQ )

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality

instance
  iLawfulEqOrdering : IsLawfulEq Ordering

  iLawfulEqOrdering .isEquality LT LT = ofY refl
  iLawfulEqOrdering .isEquality LT EQ = ofN λ()
  iLawfulEqOrdering .isEquality LT GT = ofN λ()
  iLawfulEqOrdering .isEquality EQ LT = ofN λ()
  iLawfulEqOrdering .isEquality EQ EQ = ofY refl
  iLawfulEqOrdering .isEquality EQ GT = ofN λ()
  iLawfulEqOrdering .isEquality GT LT = ofN λ()
  iLawfulEqOrdering .isEquality GT EQ = ofN λ()
  iLawfulEqOrdering .isEquality GT GT = ofY refl
  