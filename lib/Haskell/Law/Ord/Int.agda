module Haskell.Law.Ord.Int where

open import Haskell.Prim
open import Haskell.Prim.Int
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Word
open import Haskell.Prim.Ord

open import Haskell.Law.Bool
open import Haskell.Law.Equality
open import Haskell.Law.Eq
open import Haskell.Law.Ord.Def
open import Haskell.Law.Ord.Word
open import Haskell.Law.Int


sign2neq : ∀ (a b : Int) → isNegativeInt a ≡ True → isNegativeInt b ≡ False → ((a == b) ≡ False) 
sign2neq a@(int64 x) b@(int64 y) h₁ h₂ with a == b in h₃
... | False = refl --refl
... | True rewrite equality x y h₃ | sym $ h₁ = h₂

instance
  iLawfulOrdInt : IsLawfulOrd Int

  iLawfulOrdInt .comparability a@(int64 x) b@(int64 y) 
    with isNegativeInt a | isNegativeInt b 
  ... | True  | False = refl
  ... | False | True 
    rewrite ||-sym (x == y) True = refl
  ... | True  | True  = comparability x y
  ... | False | False = comparability x y 

  iLawfulOrdInt .transitivity a@(int64 x) b@(int64 y) c@(int64 z) h 
    with isNegativeInt a in h₁ | isNegativeInt b in h₂ | isNegativeInt c in h₃
  ... | True  | True  | True  =  transitivity x y z h
  ... | True  | True  | False = refl
  ... | True  | False | True  rewrite equality y z h 
    = magic $ exFalso h₃ h₂  
  ... | True  | False | False = refl
  ... | False | True  | True  rewrite equality x y (&&-leftTrue (x == y) (y <= z) h) 
    = magic $ exFalso h₂ h₁
  ... | False | True  | False rewrite equality x y (&&-leftTrue (x == y) True h) 
    = magic $ exFalso h₂ h₁
  ... | False | False | True  rewrite equality y z (&&-rightTrue (x <= y) (y == z) h) 
    = magic $ exFalso h₃ h₂ 
  ... | False | False | False = transitivity x y z h

  
  iLawfulOrdInt .reflexivity a 
    rewrite ||-sym (a < a) (a == a) 
      | eqReflexivity a 
    = refl 

  iLawfulOrdInt .antisymmetry a@(int64 x) b@(int64 y) h 
    with isNegativeInt a | isNegativeInt b 
  ... | True  | True  = antisymmetry x y h
  ... | True  | False rewrite eqSymmetry x y = h
  ... | False | True  = &&-leftTrue (x == y) True h
  ... | False | False = antisymmetry x y h

  
  iLawfulOrdInt .lte2gte (int64 x) (int64 y) 
    rewrite eqSymmetry x y 
    = refl

  iLawfulOrdInt .lt2LteNeq a@(int64 x) b@(int64 y) 
      with isNegativeInt a in h₁ | isNegativeInt b in h₂ 
  ...| True  | True  = lt2LteNeq x y
  ...| True  | False = sym $ not-involution $ sign2neq a b h₁ h₂
  ...| False | True rewrite eqSymmetry x y | sign2neq b a h₂ h₁ = refl
  ...| False | False = lt2LteNeq x y
  
  iLawfulOrdInt .lt2gt a b = refl

  iLawfulOrdInt .compareLt a@(int64 x) b@(int64 y)
    with isNegativeInt a in h₁ | isNegativeInt b in h₂ 
  ...| True  | True = compareLt x y
  ...| True  | False  = refl
  ...| False | True 
    rewrite eqSymmetry x y 
    | sign2neq b a h₂ h₁ = refl
  ...| False | False = compareLt x y

  iLawfulOrdInt .compareGt a@(int64 x) b@(int64 y)
    with isNegativeInt a in h₁ | isNegativeInt b in h₂ 
  ...| True  | True = compareGt x y
  ...| True  | False  = refl
  ...| False | True 
    rewrite eqSymmetry x y 
    | sign2neq b a h₂ h₁ = refl
  ...| False | False = compareGt x y

  iLawfulOrdInt .compareEq a@(int64 x) b@(int64 y)
      with isNegativeInt a in h₁ | isNegativeInt b in h₂ 
  ...| True  | True = compareEq x y
  ...| True  | False 
    rewrite sign2neq a b h₁ h₂ = refl
  ...| False | True 
    rewrite eqSymmetry x y | sign2neq b a h₂ h₁ = refl
  ...| False | False = compareEq x y

  iLawfulOrdInt .min2if a@(int64 x) b@(int64 y)
    with isNegativeInt a in h₁ | isNegativeInt b in h₂ 
  ...| True  | True 
    rewrite lte2ngt x y 
    | ifFlip (y < x) a b 
    = eqReflexivity (if (y < x) then b else a)
  ...| True  | False = eqReflexivity x
  ...| False | True rewrite eqSymmetry x y 
     | sign2neq b a h₂ h₁ = eqReflexivity y
  ...| False | False 
    rewrite lte2ngt x y 
    | ifFlip (y < x) a b 
    = eqReflexivity (if (y < x) then b else a) 
  
  iLawfulOrdInt .max2if a@(int64 x) b@(int64 y)
      with isNegativeInt a in h₁ | isNegativeInt b in h₂ 
  ...| False | False 
    rewrite gte2nlt x y 
    | ifFlip (x < y) a b
    = eqReflexivity (if (x < y) then b else a)
  ...| False | True  = eqReflexivity x
  ...| True  | False rewrite sign2neq a b h₁ h₂ 
    = eqReflexivity y
  ...| True  | True  
    rewrite gte2nlt x y 
    | ifFlip (x < y) a b
    = eqReflexivity (if (x < y) then b else a)
