{-# OPTIONS --erasure #-}
module Issue464Instance where

open import Haskell.Prelude
open import Issue464Class

data Unit : Type where
  MkUnit : Unit

{-# COMPILE AGDA2HS Unit #-}

instance
  iDefaultUnit : Default Unit
  iDefaultUnit .def = MkUnit
  {-# COMPILE AGDA2HS iDefaultUnit #-}

instance
  iTwoMethodsUnit : TwoMethods Unit
  iTwoMethodsUnit .methodOne = MkUnit
  iTwoMethodsUnit .methodTwo = MkUnit
  {-# COMPILE AGDA2HS iTwoMethodsUnit #-}

instance
  iProjectedBool : Projected Bool
  iProjectedBool =
    record { ProjectedMin (λ where .ProjectedMin.projected → True) }
  {-# COMPILE AGDA2HS iProjectedBool #-}

-- Module-based construction without an anonymous lambda
instance
  iProjectedNamed : Projected Int
  iProjectedNamed = record { ProjectedMin impl }
    where
      impl : ProjectedMin Int
      impl .ProjectedMin.projected = 42
  {-# COMPILE AGDA2HS iProjectedNamed #-}
