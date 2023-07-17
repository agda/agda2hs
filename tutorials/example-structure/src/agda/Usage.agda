module Usage where

open import Definition
open import Haskell.Prelude

createCountDown : Int  → Maybe CountDown
createCountDown start = if start > 0 then Just (MkCountdown start) else Nothing

{-# COMPILE AGDA2HS createCountDown #-}
