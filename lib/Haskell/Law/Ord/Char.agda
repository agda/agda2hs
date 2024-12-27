module Haskell.Law.Ord.Char where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord

open import Haskell.Law.Bool
open import Haskell.Law.Eq.Def
open import Haskell.Law.Eq.Instances
open import Haskell.Law.Ord.Def
open import Haskell.Law.Ord.Nat

instance
  iLawfulOrdChar : IsLawfulOrd Char

  iLawfulOrdChar .comparability a b 
    with (c2n a) | (c2n b) 
  ... | n | m = comparability n m

  iLawfulOrdChar .transitivity a b c h 
    with (c2n a) | (c2n b) | (c2n c)
  ... | n | m | o = transitivity n m o h

  iLawfulOrdChar .reflexivity a
    with (c2n a)
  ... | n = reflexivity n

  iLawfulOrdChar .antisymmetry a b h
    with (c2n a) | (c2n b)
  ... | n | m = antisymmetry n m h
  
  iLawfulOrdChar .lte2gte a b 
    with (c2n a) | (c2n b)
  ... | n | m = lte2gte n m

  iLawfulOrdChar .lt2LteNeq a b 
    with (c2n a) | (c2n b)
  ... | n | m = lt2LteNeq n m

  iLawfulOrdChar .lt2gt a b 
    with (c2n a) | (c2n b)
  ... | n | m = lt2gt n m

  iLawfulOrdChar .compareLt a b 
    with (c2n a) | (c2n b)
  ... | n | m = compareLt n m

  iLawfulOrdChar .compareGt a b 
    with (c2n a) | (c2n b)
  ... | n | m = compareGt n m

  iLawfulOrdChar .compareEq a b 
    with (c2n a) | (c2n b)
  ... | n | m = compareEq n m

  iLawfulOrdChar .min2if a b 
    with (c2n a) | (c2n b)
  ... | n | m 
    rewrite lte2ngt n m 
    | ifFlip (m < n) a b 
    = eqReflexivity (if (m < n) then b else a) 

  iLawfulOrdChar .max2if a b
    with (c2n a) | (c2n b)
  ... | n | m 
    rewrite gte2nlt n m
    | ifFlip (n < m) a b  
    = eqReflexivity (if (n < m) then b else a)
