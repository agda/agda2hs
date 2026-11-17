module CompileToGadtTarget where

open import Haskell.Prelude

data Res (a : Type) : Type where
  MkRes : a → Res a

{-# COMPILE AGDA2HS Res gadt #-}
