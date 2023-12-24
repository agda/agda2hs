module Issue257 where

open import Haskell.Prelude

record Wrap : Set where
  field int : Integer
{-# COMPILE AGDA2HS Wrap unboxed #-}
