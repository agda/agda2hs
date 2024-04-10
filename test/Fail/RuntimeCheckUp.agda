module Fail.RuntimeCheckUp where

open import Haskell.Prelude

conflict : (((up : Nat) → @0 IsTrue (up > 0) → Nat) → Nat) → Nat
conflict _ = 0
{-# COMPILE AGDA2HS conflict #-}
