module Fail.RuntimeCheckArg where

open import Haskell.Prelude

conflict : ((Nat → (a1 : Nat) → @0 IsTrue (a1 > 0) → Nat) → Nat) → Nat
conflict _ = 0
{-# COMPILE AGDA2HS conflict #-}
