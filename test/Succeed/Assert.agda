
open import Haskell.Prelude
open import Haskell.Control.Exception
open import Haskell.Law.Ord
open import Haskell.Extra.Dec

subtractChecked : Nat → Nat → MayThrow AssertionFailed Nat
subtractChecked x y = assert (IsFalse (x < y)) (x - y)

{-# COMPILE AGDA2HS subtractChecked #-}
