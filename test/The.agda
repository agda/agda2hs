module The where

open import Agda.Builtin.Nat
open import Haskell.Prim

five : Nat
five = the (Nat -> Nat) id 5
{-# COMPILE AGDA2HS five #-}
