module Fail.NewTypeTwoFields where

open import Haskell.Prelude

data Duo (a b : Set) : Set where
  MkDuo : a → b → Duo a b

{-# COMPILE AGDA2HS Duo newtype #-}

