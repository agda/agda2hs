module ExistingProjection where

open import Haskell.Prelude
open import Haskell.Control.Exception

projTest : AssertionFailed → String
projTest x = AssertionFailed.theFailedAssertion x
{-# COMPILE AGDA2HS projTest #-}
