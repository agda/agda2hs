module ZeroSuc where

open import Haskell.Prelude

test1 : Nat
test1 = zero

{-# COMPILE AGDA2HS test1 #-}

test2 : Nat → Nat
test2 = suc

{-# COMPILE AGDA2HS test2 #-}

data MyNat : Set where
  MyZero : MyNat
  MySuc : MyNat → MyNat

{-# COMPILE AGDA2HS MyNat #-}

opaque
  test3 : MyNat → Nat
  test3 MyZero = zero
  test3 (MySuc n) = suc (test3 n)

{-# COMPILE AGDA2HS test3 #-}
