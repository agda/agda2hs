module Haskell.Law.Ord.Integer where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord

open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Integer
open import Haskell.Law.Ord.Def
open import Haskell.Law.Ord.Nat
open import Haskell.Law.Nat

instance
  iLawfulOrdInteger : IsLawfulOrd Integer

  iLawfulOrdInteger .comparability (pos n)    (pos m)    = comparability n m
  iLawfulOrdInteger .comparability (pos n)    (negsuc m) = refl
  iLawfulOrdInteger .comparability (negsuc n) (pos m)    = refl
  iLawfulOrdInteger .comparability (negsuc n) (negsuc m)  
    rewrite sym $ lte2gte m n
    | sym $ lte2gte n m 
     = comparability m n
    
  iLawfulOrdInteger .transitivity (pos n)   (pos m)     (pos o)    h₁ = transitivity n m o h₁
  iLawfulOrdInteger .transitivity (pos n)   (pos m)     (negsuc o) h₁ 
    rewrite &&-sym (n <= m) False 
    = h₁
  iLawfulOrdInteger .transitivity (negsuc n) y          (pos o)    h₁ = refl
  iLawfulOrdInteger .transitivity (negsuc n) (negsuc m) (negsuc o) h₁ 
     rewrite eqSymmetry n o 
    = transitivity o m n (trans (reverseLte o m m n) h₁)
  
  iLawfulOrdInteger .reflexivity (pos n)    = reflexivity n
  iLawfulOrdInteger .reflexivity (negsuc n) = reflexivity n
  
  iLawfulOrdInteger .antisymmetry (pos n)    (pos m)    h₁ = antisymmetry n m h₁
  iLawfulOrdInteger .antisymmetry (negsuc n) (negsuc m) h₁ = antisymmetry n m 
    $ trans (reverseLte n m m n) h₁
  
  iLawfulOrdInteger .lte2gte (pos n)    (pos m) 
    rewrite eqSymmetry n m 
    = refl
  iLawfulOrdInteger .lte2gte (pos n)    (negsuc m) = refl
  iLawfulOrdInteger .lte2gte (negsuc n) (pos m)    = refl
  iLawfulOrdInteger .lte2gte (negsuc n) (negsuc m) 
    rewrite eqSymmetry n m 
    = refl
    
  iLawfulOrdInteger .lt2LteNeq (pos n)    (pos m)    = lt2LteNeq n m
  iLawfulOrdInteger .lt2LteNeq (pos n)    (negsuc m) = refl
  iLawfulOrdInteger .lt2LteNeq (negsuc n) (pos m)   = refl
  iLawfulOrdInteger .lt2LteNeq (negsuc n) (negsuc m) 
    rewrite eqSymmetry n m 
    = lt2LteNeq m n
  
  iLawfulOrdInteger .lt2gt x y = refl
  
  iLawfulOrdInteger .compareLt (pos n)    (pos m)    = compareLt n m
  iLawfulOrdInteger .compareLt (pos n)    (negsuc m) = refl
  iLawfulOrdInteger .compareLt (negsuc n) (pos m)    = refl
  iLawfulOrdInteger .compareLt (negsuc n) (negsuc m) 
    rewrite eqSymmetry n m 
    = compareLt m n
  
  iLawfulOrdInteger .compareGt (pos n)    (pos m)    = compareGt n m 
  iLawfulOrdInteger .compareGt (pos n)    (negsuc m) = refl
  iLawfulOrdInteger .compareGt (negsuc n) (pos m)    = refl
  iLawfulOrdInteger .compareGt (negsuc n) (negsuc m) 
    rewrite eqSymmetry n m 
    = compareGt m n
  
  iLawfulOrdInteger .compareEq (pos n)    (pos m)    = compareEq n m
  iLawfulOrdInteger .compareEq (pos n)    (negsuc m) = refl
  iLawfulOrdInteger .compareEq (negsuc n) (pos m)    = refl
  iLawfulOrdInteger .compareEq (negsuc n) (negsuc m) 
    rewrite eqSymmetry n m 
    = compareEq m n
  
  iLawfulOrdInteger .min2if (pos n)    (pos m) 
    rewrite lte2ngt n m
    | sym $ ifFlip (m < n) (pos m) (pos n)  
    = eqReflexivity (min (pos n) (pos m))
  iLawfulOrdInteger .min2if (pos n)    (negsuc m) = eqReflexivity m
  iLawfulOrdInteger .min2if (negsuc n) (pos m)    = eqReflexivity n
  iLawfulOrdInteger .min2if (negsuc n) (negsuc m) 
    rewrite gte2nlt n m  
    | sym $ ifFlip (n < m) (negsuc m) (negsuc n) 
    = eqReflexivity (min (negsuc n) (negsuc m)) 
   
  iLawfulOrdInteger .max2if (pos n)    (pos m) 
    rewrite gte2nlt n m 
    | sym (ifFlip (n < m) (pos m) (pos n))  
    = eqReflexivity (max (pos n) (pos m)) 
  iLawfulOrdInteger .max2if (pos n)    (negsuc m) = eqReflexivity n  
  iLawfulOrdInteger .max2if (negsuc n) (pos m)    = eqReflexivity m 
  iLawfulOrdInteger .max2if (negsuc n) (negsuc m) 
    rewrite lte2ngt n m
    | sym $ ifFlip (m < n) (negsuc m) (negsuc n) 
    = eqReflexivity (max (negsuc n) (negsuc m))
