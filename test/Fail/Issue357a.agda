open import Haskell.Prelude
open import Agda.Primitive

module Issue357a where

k : a → b → a
k x _ = x
{-# COMPILE AGDA2HS k #-}

testK : Nat
testK = k 42 lzero
{-# COMPILE AGDA2HS testK #-}
