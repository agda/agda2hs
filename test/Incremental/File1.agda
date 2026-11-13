module File1 where

open import Haskell.Prelude

private variable
  @0 n : Nat

data Vec (a : Type) : @0 Nat → Type where
  []  : Vec a zero
  _∷_ : a → Vec a n → Vec a (suc n)
{-# COMPILE AGDA2HS Vec to List #-}

foo : Vec a 0
foo = []
{-# COMPILE AGDA2HS foo #-}

num : Nat
num = 42
{-# COMPILE AGDA2HS num inline #-}
