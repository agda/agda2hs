
open import Haskell.Prelude
open import Haskell.Control.Exception
open import Agda2Hs.Law.Ord
open import Agda2Hs.Extra.Dec

subtractChecked : Nat → Nat → Nat
subtractChecked x y = assert (IsFalse (x < y)) (x - y)

{-# COMPILE AGDA2HS subtractChecked #-}
