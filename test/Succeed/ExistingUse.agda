module ExistingUse where

open import Haskell.Prelude
open import Existing using (existingFun)

useExistingImported : Int
useExistingImported = existingFun
{-# COMPILE AGDA2HS useExistingImported #-}
