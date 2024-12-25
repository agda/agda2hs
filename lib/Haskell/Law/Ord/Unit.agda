module Haskell.Law.Ord.Unit where

open import Haskell.Prim
open import Haskell.Prim.Ord

open import Haskell.Law.Ord.Def
open import Haskell.Law.Eq.Instances

instance
  iLawfulOrdUnit : IsLawfulOrd ⊤

  iLawfulOrdUnit .comparability _ _ = refl
  iLawfulOrdUnit .transitivity _ _ _ _ = refl
  iLawfulOrdUnit .reflexivity _ = refl
  iLawfulOrdUnit .antisymmetry _ _ _ = refl
  iLawfulOrdUnit .lte2gte _ _ = refl
  iLawfulOrdUnit .lt2LteNeq _ _ = refl
  iLawfulOrdUnit .lt2gt _ _ = refl
  iLawfulOrdUnit .compareLt _ _ = refl
  iLawfulOrdUnit .compareGt _ _ = refl
  iLawfulOrdUnit .compareEq _ _ = refl
  iLawfulOrdUnit .min2if _ _ = refl
  iLawfulOrdUnit .max2if _ _ = refl
