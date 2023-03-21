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

  iLawfulOrdOrdering .compareLt LT LT = refl
  iLawfulOrdOrdering .compareLt LT EQ = refl
  iLawfulOrdOrdering .compareLt LT GT = refl
  iLawfulOrdOrdering .compareLt EQ LT = refl
  iLawfulOrdOrdering .compareLt EQ EQ = refl
  iLawfulOrdOrdering .compareLt EQ GT = refl
  iLawfulOrdOrdering .compareLt GT LT = refl
  iLawfulOrdOrdering .compareLt GT EQ = refl
  iLawfulOrdOrdering .compareLt GT GT = refl

  iLawfulOrdOrdering .compareGt LT LT = refl
  iLawfulOrdOrdering .compareGt LT EQ = refl
  iLawfulOrdOrdering .compareGt LT GT = refl
  iLawfulOrdOrdering .compareGt EQ LT = refl
  iLawfulOrdOrdering .compareGt EQ EQ = refl
  iLawfulOrdOrdering .compareGt EQ GT = refl
  iLawfulOrdOrdering .compareGt GT LT = refl
  iLawfulOrdOrdering .compareGt GT EQ = refl
  iLawfulOrdOrdering .compareGt GT GT = refl

  iLawfulOrdOrdering .compareEq LT LT = refl
  iLawfulOrdOrdering .compareEq LT EQ = refl
  iLawfulOrdOrdering .compareEq LT GT = refl
  iLawfulOrdOrdering .compareEq EQ LT = refl
  iLawfulOrdOrdering .compareEq EQ EQ = refl
  iLawfulOrdOrdering .compareEq EQ GT = refl
  iLawfulOrdOrdering .compareEq GT LT = refl
  iLawfulOrdOrdering .compareEq GT EQ = refl
  iLawfulOrdOrdering .compareEq GT GT = refl

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
  