module Fail.RuntimeCheckUnboxed where

open import Haskell.Prelude

record Unboxable : Set where
  -- The erasure is in an evenly nested position, keeping the record unboxable.
  field unboxField : (@0 _ : IsTrue Bool.true → Nat) → Nat
{-# COMPILE AGDA2HS Unboxable unboxed #-}

record NotUnboxable : Set where
  field noUnboxField : (@0 _ : IsTrue Bool.true) → Nat
{-# COMPILE AGDA2HS NotUnboxable unboxed #-}
