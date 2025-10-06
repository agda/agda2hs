module Definition where

open import Haskell.Prelude

data CountDown : Type where
    MkCountdown : (start  : Int)
            → {{ @0 h : ((start > 0) ≡ True) }}
            → CountDown

{-# COMPILE AGDA2HS CountDown #-}
