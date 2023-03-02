module Fail.PartialCase where

open import Haskell.Prelude

caseOf : (i : Int) → ((i' : Int) → @0 {{ i ≡ i' }} → Nat) → Nat
caseOf = case_of_
{-# COMPILE AGDA2HS caseOf #-}
