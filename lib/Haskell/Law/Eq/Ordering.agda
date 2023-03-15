module Haskell.Law.Eq.Ordering where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord using ( Ordering; LT; GT; EQ )

open import Haskell.Law.Eq.Def

instance
  iLawfulEqOrdering : IsLawfulEq Ordering

  iLawfulEqOrdering .equality LT LT _ = refl
  iLawfulEqOrdering .equality EQ EQ _ = refl
  iLawfulEqOrdering .equality GT GT _ = refl

  iLawfulEqOrdering .nequality LT EQ _ = λ()
  iLawfulEqOrdering .nequality LT GT _ = λ()
  iLawfulEqOrdering .nequality EQ LT _ = λ()
  iLawfulEqOrdering .nequality EQ GT _ = λ()
  iLawfulEqOrdering .nequality GT LT _ = λ()
  iLawfulEqOrdering .nequality GT EQ _ = λ()
  