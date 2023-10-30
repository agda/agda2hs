open import Haskell.Prelude hiding (f)

record Test (a : Set) : Set₁ where
  field
    f : a -> a
open Test {{...}} public
{-# COMPILE AGDA2HS Test class #-}

instance
  testNat : Test Nat
  Test.f testNat n = h
    where
    g : Nat
    g = 3 + n
    h : Nat
    h = n + g
  {-# COMPILE AGDA2HS testNat #-}

f1 : Nat -> Nat
f1 n = h1
  where
  g1 : Nat
  g1 = 3 + n
  h1 : Nat
  h1 = n + g1
{-# COMPILE AGDA2HS f1 #-}

f2 : Nat -> Nat
f2 n = h2 n
  where
  g2 : Nat
  g2 = 3 + n
  h2 : Nat -> Nat
  h2 m = n + g2 + m
{-# COMPILE AGDA2HS f2 #-}
