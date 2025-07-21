{-# OPTIONS --sized-types #-}
module RuntimeCheckCallFeatures where

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import RuntimeCheckFeatures

externalFunCaller : Nat
externalFunCaller = simpleFun 1
{-# COMPILE AGDA2HS externalFunCaller #-}
