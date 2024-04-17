module Haskell.Law.Ord.Nat where
    
open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord

open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Ord.Def
open import Haskell.Law.Nat

instance
  iLawfulOrdNat : IsLawfulOrd Nat

  iLawfulOrdNat .comparability zero    zero    = refl
  iLawfulOrdNat .comparability zero    (suc y) = refl
  iLawfulOrdNat .comparability (suc x) zero    = refl
  iLawfulOrdNat .comparability (suc x) (suc y) 
    rewrite comparability x y 
    = refl

  iLawfulOrdNat .transitivity zero    y       zero    h₁ = refl
  iLawfulOrdNat .transitivity zero    y       (suc z) h₁ = refl
  iLawfulOrdNat .transitivity (suc x) (suc y) zero    h₁ 
    rewrite &&-sym (x <= y) False  
    = h₁ 
  iLawfulOrdNat .transitivity (suc x) (suc y) (suc z) h₁ = transitivity x y z h₁
  
  iLawfulOrdNat .reflexivity zero    = refl
  iLawfulOrdNat .reflexivity (suc x) = reflexivity x
  
  iLawfulOrdNat .antisymmetry zero    zero    h₁ = refl
  iLawfulOrdNat .antisymmetry (suc x) (suc y) h₁ = antisymmetry x y h₁ 

  iLawfulOrdNat .lte2gte zero    zero    = refl
  iLawfulOrdNat .lte2gte zero    (suc y) = refl
  iLawfulOrdNat .lte2gte (suc x) zero    = refl
  iLawfulOrdNat .lte2gte (suc x) (suc y) = lte2gte x y
  
  iLawfulOrdNat .lt2LteNeq zero    zero    = refl
  iLawfulOrdNat .lt2LteNeq zero    (suc y) = refl
  iLawfulOrdNat .lt2LteNeq (suc x) zero    = refl
  iLawfulOrdNat .lt2LteNeq (suc x) (suc y) = lt2LteNeq x y

  iLawfulOrdNat .lt2gt zero    y = refl
  iLawfulOrdNat .lt2gt (suc x) y = refl
  
  iLawfulOrdNat .compareLt zero    zero    = refl
  iLawfulOrdNat .compareLt zero    (suc y) = refl
  iLawfulOrdNat .compareLt (suc x) zero    = refl
  iLawfulOrdNat .compareLt (suc x) (suc y) = compareLt x y
   
  iLawfulOrdNat .compareGt zero    zero    = refl
  iLawfulOrdNat .compareGt zero    (suc y) = refl
  iLawfulOrdNat .compareGt (suc x) zero    = refl
  iLawfulOrdNat .compareGt (suc x) (suc y) = compareGt x y
   
  iLawfulOrdNat .compareEq zero    zero    = refl
  iLawfulOrdNat .compareEq zero    (suc y) = refl
  iLawfulOrdNat .compareEq (suc x) zero    = refl
  iLawfulOrdNat .compareEq (suc x) (suc y) = compareEq x y 

  iLawfulOrdNat .min2if zero    zero                      = refl
  iLawfulOrdNat .min2if zero    (suc y)                   = refl
  iLawfulOrdNat .min2if (suc x) zero                      = refl
  iLawfulOrdNat .min2if (suc x) (suc y) with x <= y in h₁ 
  ... | True 
    rewrite (cong (min x y ==_) (sym $ ifTrueEqThen (x <= y) {x} {y} h₁)) 
    = min2if x y
  ... | False 
    rewrite (cong (min x y ==_) (sym $ ifFalseEqElse (x <= y) {x} {y} h₁)) 
    = min2if x y
            
  iLawfulOrdNat .max2if zero    zero                        = refl
  iLawfulOrdNat .max2if zero    (suc y)                     = eqReflexivity y
  iLawfulOrdNat .max2if (suc x) zero                        = eqReflexivity x
  iLawfulOrdNat .max2if (suc x) (suc y) with x >= y in h₁
  ... | True 
    rewrite (cong (max x y ==_) (sym $ ifTrueEqThen (x >= y) {x} {y} h₁)) 
    = max2if x y    
  ... | False 
    rewrite (cong (max x y ==_) (sym $ ifFalseEqElse (x >= y) {x} {y} h₁)) 
    = max2if x y
