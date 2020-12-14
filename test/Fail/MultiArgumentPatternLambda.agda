
module Fail.MultiArgumentPatternLambda where

open import Agda.Builtin.Bool

tooManyPats : Bool → Bool → Bool
tooManyPats = λ where false false → false
                      true  true  → false
                      _     _     → true
{-# COMPILE AGDA2HS tooManyPats #-}
