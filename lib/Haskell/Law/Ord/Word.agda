module Haskell.Law.Ord.Word where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Word   using ( Word )

open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Ord.Def
open import Haskell.Law.Ord.Nat

instance
  iLawfulOrdWord : IsLawfulOrd Word

  iLawfulOrdWord .comparability a b 
    with (w2n a) | (w2n b)
  ... | x | y  = comparability x y
  
  iLawfulOrdWord .transitivity a b c h 
     with (w2n a) | (w2n b) | (w2n c) 
  ... | x  | y | z = transitivity x y z h 
  
  iLawfulOrdWord .reflexivity a 
    with (w2n a)
  ... | x = reflexivity x

  iLawfulOrdWord .antisymmetry a b h 
    with (w2n a) | (w2n b) 
  ... | x | y = antisymmetry x y h 

  iLawfulOrdWord .lte2gte a b
    with (w2n a) | (w2n b) 
  ... | x | y = lte2gte x y 

  iLawfulOrdWord .lt2LteNeq a b 
    with (w2n a) | (w2n b) 
  ... | x | y = lt2LteNeq x y

  iLawfulOrdWord .lt2gt a b 
    with (w2n a) | (w2n b) 
  ... | x | y = lt2gt x y

  iLawfulOrdWord .compareLt a b 
    with (w2n a) | (w2n b) 
  ... | x | y = compareLt x y
  
  iLawfulOrdWord .compareGt a b
    with (w2n a) | (w2n b) 
  ... | x | y = compareGt x y
  
  iLawfulOrdWord .compareEq a b
    with (w2n a) | (w2n b) 
  ... | x | y =  compareEq x y
  
  iLawfulOrdWord .min2if a b
    with (w2n a) | (w2n b)  
  ... | x | y 
    rewrite lte2ngt x y 
    | ifFlip (y < x) a b 
    = eqReflexivity (if (y < x) then b else a) 
  
  iLawfulOrdWord .max2if a b 
    with (w2n a) | (w2n b)  
  ... | x | y 
    rewrite gte2nlt x y
    | ifFlip (x < y) a b  
    = eqReflexivity (if (x < y) then b else a) 