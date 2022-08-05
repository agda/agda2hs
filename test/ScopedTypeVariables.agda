module ScopedTypeVariables where

open import Haskell.Prelude

f : a → Bool
f x = it x == x
  where
    it : a -> a
    it = const x
{-# COMPILE AGDA2HS f #-}
