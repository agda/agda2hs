module Haskell.Law.Eq.Ordering where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord using ( Ordering; LT; GT; EQ )

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality

instance
  iLawfulEqOrdering : IsLawfulEq Ordering

  iLawfulEqOrdering .isEquality LT LT = refl
  iLawfulEqOrdering .isEquality LT EQ = λ()
  iLawfulEqOrdering .isEquality LT GT = λ()
  iLawfulEqOrdering .isEquality EQ LT = λ()
  iLawfulEqOrdering .isEquality EQ EQ = refl
  iLawfulEqOrdering .isEquality EQ GT = λ()
  iLawfulEqOrdering .isEquality GT LT = λ()
  iLawfulEqOrdering .isEquality GT EQ = λ()
  iLawfulEqOrdering .isEquality GT GT = refl

