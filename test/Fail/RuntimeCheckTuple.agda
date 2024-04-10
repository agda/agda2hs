module Fail.RuntimeCheckTuple where

open import Haskell.Prelude

record CanTuple : Set where
  field tupleField : Nat
{-# COMPILE AGDA2HS CanTuple tuple #-}

record CantTuple : Set where
  field tupleField : (@0 _ : IsTrue Bool.true) → Nat
{-# COMPILE AGDA2HS CantTuple tuple #-}
