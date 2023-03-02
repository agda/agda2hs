module Fail.PartialCaseNoLambda where

open import Haskell.Prelude

applyToFalse : ((b : Bool) → @0 {{ False ≡ b }} → Int) → Int
applyToFalse = case False of_
{-# COMPILE AGDA2HS applyToFalse #-}
