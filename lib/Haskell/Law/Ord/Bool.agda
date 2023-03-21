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

  iLawfulOrdBool .compareLt False False = refl
  iLawfulOrdBool .compareLt False True  = refl
  iLawfulOrdBool .compareLt True  False = refl
  iLawfulOrdBool .compareLt True  True  = refl

  iLawfulOrdBool .compareGt False False = refl
  iLawfulOrdBool .compareGt False True  = refl
  iLawfulOrdBool .compareGt True  False = refl
  iLawfulOrdBool .compareGt True  True  = refl

  iLawfulOrdBool .compareEq False False = refl
  iLawfulOrdBool .compareEq False True  = refl
  iLawfulOrdBool .compareEq True  False = refl
  iLawfulOrdBool .compareEq True  True  = refl

  iLawfulOrdBool .min2if False False = refl
  iLawfulOrdBool .min2if False True  = refl
  iLawfulOrdBool .min2if True  False = refl
  iLawfulOrdBool .min2if True  True  = refl
  
  iLawfulOrdBool .max2if False False = refl
  iLawfulOrdBool .max2if False True  = refl
  iLawfulOrdBool .max2if True  False = refl
  iLawfulOrdBool .max2if True  True  = refl
 