{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Real where

open import Haskell.Prim
open import Haskell.Prim.Rational
open import Haskell.Prim.Int
open import Haskell.Prim.Integer
open import Haskell.Prim.RealFrac
open import Haskell.Prim.Word
open import Haskell.Prim.Double

--------------------------------------------------
-- Real

record Real (a : Set) : Set where
  field
    toRational : a → Rational
open Real ⦃... ⦄  public

{-# COMPILE AGDA2HS Real existing-class #-}

instance
  iRealNat : Real Nat
  iRealNat.toRational x = x :% 1
  
  iRealInt : Real Int
  iRealInt.toRational x = toInteger x :% 1
  
  iRealInteger : Real Integer
  iRealInteger.toRational x = x :% 1
  
  iRealWord : Real Word
  iRealWord.toRational x = toInteger x :% 1  
  
--------------------------------------------------
-- Arithmetic


--------------------------------------------------
-- Constraints

isNegativeReal : a → Bool
isNegativeReal (pos _)    = False
isNegativeReal (negsuc _) = True

IsNonNegativeReal : a → Set
IsNonNegativeReal (pos _)      = ⊤
IsNonNegativeReal n@(negsuc _) =
  TypeError (primStringAppend (primShowReal n) (" is negative"))
