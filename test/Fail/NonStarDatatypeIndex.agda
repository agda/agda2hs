module Fail.NonStarDatatypeIndex where

open import Haskell.Prelude

data T (n : Nat) : Type where
  MkT : T n
{-# COMPILE AGDA2HS T #-}
