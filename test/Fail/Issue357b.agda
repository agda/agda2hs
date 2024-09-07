open import Haskell.Prelude
open import Agda.Primitive

module Fail.Issue357b where

k : a → b → a
k x _ = x
{-# COMPILE AGDA2HS k #-}

l : Level → Nat
l = k 42
{-# COMPILE AGDA2HS l #-}

testK : Nat
testK = l lzero
{-# COMPILE AGDA2HS testK #-}
