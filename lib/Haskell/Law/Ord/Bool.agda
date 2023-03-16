{-# OPTIONS --allow-unsolved-metas #-}

module Haskell.Law.Ord.Bool where

open import Haskell.Prim
open import Haskell.Prim.Ord

open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Ord.Def

instance
  iLawfulOrdBool : IsLawfulOrd Bool
  
  iLawfulOrdBool .comparability False False = refl
  iLawfulOrdBool .comparability False True  = refl
  iLawfulOrdBool .comparability True  False = refl
  iLawfulOrdBool .comparability True  True  = refl

  iLawfulOrdBool .transitivity False False False _ = refl
  iLawfulOrdBool .transitivity False False True  _ = refl
  iLawfulOrdBool .transitivity False True  True  _ = refl
  iLawfulOrdBool .transitivity True  True  True  _ = refl

  iLawfulOrdBool .reflexivity False = refl
  iLawfulOrdBool .reflexivity True  = refl

  iLawfulOrdBool .antisymmetry False False _ = refl
  iLawfulOrdBool .antisymmetry True  True  _ = refl

  iLawfulOrdBool .lte2gte False False = refl
  iLawfulOrdBool .lte2gte False True  = refl
  iLawfulOrdBool .lte2gte True  False = refl
  iLawfulOrdBool .lte2gte True  True  = refl

  iLawfulOrdBool .lNotLteNeq False False = refl
  iLawfulOrdBool .lNotLteNeq False True  = refl
  iLawfulOrdBool .lNotLteNeq True  False = refl
  iLawfulOrdBool .lNotLteNeq True  True  = refl

  iLawfulOrdBool .lt2gt False False = refl
  iLawfulOrdBool .lt2gt False True  = refl
  iLawfulOrdBool .lt2gt True  False = refl
  iLawfulOrdBool .lt2gt True  True  = refl

  iLawfulOrdBool .isCompareLt False False = ofN λ()
  iLawfulOrdBool .isCompareLt False True  = ofY refl
  iLawfulOrdBool .isCompareLt True  False = ofN λ()
  iLawfulOrdBool .isCompareLt True  True  = ofN λ()

  iLawfulOrdBool .isCompareGt False False = ofN λ()
  iLawfulOrdBool .isCompareGt False True  = ofN λ()
  iLawfulOrdBool .isCompareGt True  False = ofY refl
  iLawfulOrdBool .isCompareGt True  True  = ofN λ()

  iLawfulOrdBool .isCompareEq False False = ofY refl
  iLawfulOrdBool .isCompareEq False True  = ofN λ()
  iLawfulOrdBool .isCompareEq True  False = ofN λ()
  iLawfulOrdBool .isCompareEq True  True  = ofY refl

  iLawfulOrdBool .min2if False False = refl
  iLawfulOrdBool .min2if False True  = refl
  iLawfulOrdBool .min2if True  False = refl
  iLawfulOrdBool .min2if True  True  = refl
  
  iLawfulOrdBool .max2if False False = refl
  iLawfulOrdBool .max2if False True  = refl
  iLawfulOrdBool .max2if True  False = refl
  iLawfulOrdBool .max2if True  True  = refl
 