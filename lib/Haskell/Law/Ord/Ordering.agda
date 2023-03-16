module Haskell.Law.Ord.Ordering where

open import Haskell.Prim
open import Haskell.Prim.Ord

open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Ord.Def

instance
  iLawfulOrdOrdering : IsLawfulOrd Ordering
  
  iLawfulOrdOrdering .comparability LT LT = refl
  iLawfulOrdOrdering .comparability LT EQ = refl
  iLawfulOrdOrdering .comparability LT GT = refl
  iLawfulOrdOrdering .comparability EQ LT = refl
  iLawfulOrdOrdering .comparability EQ EQ = refl
  iLawfulOrdOrdering .comparability EQ GT = refl
  iLawfulOrdOrdering .comparability GT LT = refl
  iLawfulOrdOrdering .comparability GT EQ = refl
  iLawfulOrdOrdering .comparability GT GT = refl

  iLawfulOrdOrdering .transitivity LT LT LT _ = refl
  iLawfulOrdOrdering .transitivity LT LT EQ _ = refl
  iLawfulOrdOrdering .transitivity LT LT GT _ = refl
  iLawfulOrdOrdering .transitivity LT EQ EQ _ = refl
  iLawfulOrdOrdering .transitivity LT EQ GT _ = refl
  iLawfulOrdOrdering .transitivity LT GT GT _ = refl
  iLawfulOrdOrdering .transitivity EQ EQ EQ _ = refl
  iLawfulOrdOrdering .transitivity EQ EQ GT _ = refl
  iLawfulOrdOrdering .transitivity EQ GT GT _ = refl
  iLawfulOrdOrdering .transitivity GT GT GT _ = refl

  iLawfulOrdOrdering .reflexivity LT = refl
  iLawfulOrdOrdering .reflexivity EQ = refl
  iLawfulOrdOrdering .reflexivity GT = refl

  iLawfulOrdOrdering .antisymmetry LT LT _ = refl
  iLawfulOrdOrdering .antisymmetry EQ EQ _ = refl
  iLawfulOrdOrdering .antisymmetry GT GT _ = refl

  iLawfulOrdOrdering .lte2gte LT LT = refl
  iLawfulOrdOrdering .lte2gte LT EQ = refl
  iLawfulOrdOrdering .lte2gte LT GT = refl
  iLawfulOrdOrdering .lte2gte EQ LT = refl
  iLawfulOrdOrdering .lte2gte EQ EQ = refl
  iLawfulOrdOrdering .lte2gte EQ GT = refl
  iLawfulOrdOrdering .lte2gte GT LT = refl
  iLawfulOrdOrdering .lte2gte GT EQ = refl
  iLawfulOrdOrdering .lte2gte GT GT = refl

  iLawfulOrdOrdering .lNotLteNeq LT LT = refl
  iLawfulOrdOrdering .lNotLteNeq LT EQ = refl
  iLawfulOrdOrdering .lNotLteNeq LT GT = refl
  iLawfulOrdOrdering .lNotLteNeq EQ LT = refl
  iLawfulOrdOrdering .lNotLteNeq EQ EQ = refl
  iLawfulOrdOrdering .lNotLteNeq EQ GT = refl
  iLawfulOrdOrdering .lNotLteNeq GT LT = refl
  iLawfulOrdOrdering .lNotLteNeq GT EQ = refl
  iLawfulOrdOrdering .lNotLteNeq GT GT = refl

  iLawfulOrdOrdering .lt2gt LT LT = refl
  iLawfulOrdOrdering .lt2gt LT EQ = refl
  iLawfulOrdOrdering .lt2gt LT GT = refl
  iLawfulOrdOrdering .lt2gt EQ LT = refl
  iLawfulOrdOrdering .lt2gt EQ EQ = refl
  iLawfulOrdOrdering .lt2gt EQ GT = refl
  iLawfulOrdOrdering .lt2gt GT LT = refl
  iLawfulOrdOrdering .lt2gt GT EQ = refl
  iLawfulOrdOrdering .lt2gt GT GT = refl

  iLawfulOrdOrdering .isCompareLt LT LT = ofN λ()
  iLawfulOrdOrdering .isCompareLt LT EQ = ofY refl
  iLawfulOrdOrdering .isCompareLt LT GT = ofY refl
  iLawfulOrdOrdering .isCompareLt EQ LT = ofN λ()
  iLawfulOrdOrdering .isCompareLt EQ EQ = ofN λ()
  iLawfulOrdOrdering .isCompareLt EQ GT = ofY refl
  iLawfulOrdOrdering .isCompareLt GT LT = ofN λ()
  iLawfulOrdOrdering .isCompareLt GT EQ = ofN λ()
  iLawfulOrdOrdering .isCompareLt GT GT = ofN λ()

  iLawfulOrdOrdering .isCompareGt LT LT = ofN λ()
  iLawfulOrdOrdering .isCompareGt LT EQ = ofN λ()
  iLawfulOrdOrdering .isCompareGt LT GT = ofN λ()
  iLawfulOrdOrdering .isCompareGt EQ LT = ofY refl
  iLawfulOrdOrdering .isCompareGt EQ EQ = ofN λ()
  iLawfulOrdOrdering .isCompareGt EQ GT = ofN λ()
  iLawfulOrdOrdering .isCompareGt GT LT = ofY refl
  iLawfulOrdOrdering .isCompareGt GT EQ = ofY refl
  iLawfulOrdOrdering .isCompareGt GT GT = ofN λ()

  iLawfulOrdOrdering .isCompareEq LT LT = ofY refl
  iLawfulOrdOrdering .isCompareEq LT EQ = ofN λ()
  iLawfulOrdOrdering .isCompareEq LT GT = ofN λ()
  iLawfulOrdOrdering .isCompareEq EQ LT = ofN λ()
  iLawfulOrdOrdering .isCompareEq EQ EQ = ofY refl
  iLawfulOrdOrdering .isCompareEq EQ GT = ofN λ()
  iLawfulOrdOrdering .isCompareEq GT LT = ofN λ()
  iLawfulOrdOrdering .isCompareEq GT EQ = ofN λ()
  iLawfulOrdOrdering .isCompareEq GT GT = ofY refl

  iLawfulOrdOrdering .min2if LT LT = refl
  iLawfulOrdOrdering .min2if LT EQ = refl
  iLawfulOrdOrdering .min2if LT GT = refl
  iLawfulOrdOrdering .min2if EQ LT = refl
  iLawfulOrdOrdering .min2if EQ EQ = refl
  iLawfulOrdOrdering .min2if EQ GT = refl
  iLawfulOrdOrdering .min2if GT LT = refl
  iLawfulOrdOrdering .min2if GT EQ = refl
  iLawfulOrdOrdering .min2if GT GT = refl
  
  iLawfulOrdOrdering .max2if LT LT = refl
  iLawfulOrdOrdering .max2if LT EQ = refl
  iLawfulOrdOrdering .max2if LT GT = refl
  iLawfulOrdOrdering .max2if EQ LT = refl
  iLawfulOrdOrdering .max2if EQ EQ = refl
  iLawfulOrdOrdering .max2if EQ GT = refl
  iLawfulOrdOrdering .max2if GT LT = refl
  iLawfulOrdOrdering .max2if GT EQ = refl
  iLawfulOrdOrdering .max2if GT GT = refl
  