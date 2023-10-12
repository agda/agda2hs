module Fail.NonCanonicalSpecialFunction where

open import Haskell.Prelude

sneaky : Enum Int
Enum.BoundedBelowEnum sneaky = Just (record { minBound = 42 })
Enum.BoundedAboveEnum sneaky = Just (record { maxBound = 42 })
Enum.fromEnum sneaky = λ _ → 42
Enum.toEnum sneaky = λ _ → 42
Enum.succ sneaky = λ _ → 42
Enum.pred sneaky = λ _ → 42
Enum.enumFrom sneaky = λ _ → []
Enum.enumFromTo sneaky = λ _ _ → []
Enum.enumFromThenTo sneaky = λ _ _ _ → []
Enum.enumFromThen sneaky = λ _ _ → []

test : List Int
test = enumFrom {{sneaky}} 5

proof : test ≡ []
proof = refl

{-# COMPILE AGDA2HS test #-}
