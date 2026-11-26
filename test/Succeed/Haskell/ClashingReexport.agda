module Haskell.ClashingReexport where

open import Haskell.Prelude

foo : Nat
foo = 42
{-# COMPILE AGDA2HS foo existing #-}
