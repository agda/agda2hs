module Fail.NewTypeTwoConstructors where

open import Haskell.Prelude

data Choice (a b  : Type) : Type where
  A : a → Choice a b
  B : b → Choice a b

{-# COMPILE AGDA2HS Choice newtype #-}

