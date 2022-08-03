
module Numbers where

open import Haskell.Prelude

posNatural : Nat
posNatural = 14

posInteger : Integer
posInteger = 52

negInteger : Integer
negInteger = -1001

natToPos : Nat → Integer
natToPos n = fromNat n

natToNeg : Nat → Integer
natToNeg n = fromNeg n

{-# COMPILE AGDA2HS posNatural #-}
{-# COMPILE AGDA2HS posInteger #-}
{-# COMPILE AGDA2HS negInteger #-}
{-# COMPILE AGDA2HS natToPos   #-}
{-# COMPILE AGDA2HS natToNeg   #-}
