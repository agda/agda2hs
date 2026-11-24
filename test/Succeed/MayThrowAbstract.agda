module MayThrowAbstract where

open import Haskell.Prelude
open import Haskell.Control.Exception
open import Haskell.Extra.Dec

abstract
  throwing : Nat → MayThrow AssertionFailed Nat
  throwing x = assert (IsTrue (x == 0)) x

{-# COMPILE AGDA2HS throwing #-}
