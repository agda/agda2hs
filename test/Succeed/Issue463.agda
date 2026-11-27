module Issue463 where

open import Haskell.Prelude

List' : Type → Type
List' a = List a
{-# COMPILE AGDA2HS List' #-}

module _ where
  z : Nat
  z = 0
{-# COMPILE AGDA2HS z #-}
