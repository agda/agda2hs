{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Integral where

open import Haskell.Prim
open import Haskell.Prim.Integer
open import Haskell.Prim.Tuple

--------------------------------------------------
-- Integral

record Integral (a : Set) : Set where
  infixl 7 _quot_ _rem_ _div_ _mod_
  field
    _quot_ : a → a → a
    _rem_ : a → a → a
    _div_ : a → a → a
    _mod_ : a → a → a
    quotRem : a → a → (a × a)
    divMod : a → a → (a × a) 
    toInteger : a → Integer
open Integral ⦃...⦄ public

{-# COMPILE AGDA2HS Integral existing-class #-}

instance
  iIntegralNat : Integral Nat
  iIntegralNat._quot_ n d = ?
  iIntegralNat._rem_ n d = ?
  iIntegralNat._div_ n d = ?
  iIntegralNat.quotRem n d = ?
  iIntegralNat.toInteger x = toInteger x
  
  iIntegralInt : Integral Int
  iIntegralInt._quot_ n d = ?
  iIntegralInt._rem_ n d = ?
  iIntegralInt._div_ n d = ?
  iIntegralInt.quotRem n d = ?
  iIntegralInt.toInteger x = toInteger x
  
  iIntegralInteger : Integral Integer
  iIntegralInteger._quot_ n d = ?
  iIntegralInteger._rem_ n d = ?
  iIntegralInteger._div_ n d = ?
  iIntegralInteger.quotRem n d = ?
  iIntegralInteger.toInteger x = toInteger x
  
  iIntegralWord : Integral Word
  iIntegralWord._quot_ n d = ?
  iIntegralWord._rem_ n d = ?
  iIntegralWord._div_ n d =?
  iIntegralWord.quotRem n d = ?
  iIntegralWord.toInteger x = toInteger x
