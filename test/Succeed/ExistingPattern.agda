module ExistingPattern where

open import Haskell.Prelude
open import Haskell.Control.Exception

mkAF : String → AssertionFailed
mkAF s = record { theFailedAssertion = s }
{-# COMPILE AGDA2HS mkAF #-}

getAF : AssertionFailed → String
getAF (record { theFailedAssertion = s }) = s
{-# COMPILE AGDA2HS getAF #-}
