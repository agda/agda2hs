module Fail.Inline where

open import Haskell.Prelude

tail' : List a → List a
tail' (x ∷ xs) = xs
tail' [] = []
{-# COMPILE AGDA2HS tail' inline #-}

test : List a → List a
test = tail'

{-# COMPILE AGDA2HS test #-}
