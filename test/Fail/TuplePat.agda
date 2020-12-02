
module Fail.TuplePat where

open import Haskell.Prelude

fst₃ : a × b × c → a
fst₃ (x ∷ xs) = x

{-# COMPILE AGDA2HS fst₃ #-}
