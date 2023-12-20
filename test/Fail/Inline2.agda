module Fail.Inline2 where

open import Haskell.Prelude

tail' : (xs : List a) → @0 {{ NonEmpty xs }}  → List a
tail' (x ∷ xs) = xs
{-# COMPILE AGDA2HS tail' inline #-}
