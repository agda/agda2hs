
module Fail.MatchOnDelay where

open import Haskell.Prelude
open import Haskell.Extra.Delay

bad : Delay a ∞ → Bool
bad (now x) = True
bad (later x) = False

{-# COMPILE AGDA2HS bad #-}
