module Issue257 where

open import Haskell.Prelude

record Wrap : Type where
  field int : Integer
{-# COMPILE AGDA2HS Wrap unboxed #-}
