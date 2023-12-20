module Fail.Inline where

open import Haskell.Prelude

tail' : List a → List a
tail' (x ∷ xs) = xs
tail' [] = []
{-# COMPILE AGDA2HS tail' inline #-}
