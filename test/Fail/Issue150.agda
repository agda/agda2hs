module Fail.Issue150 where

open import Haskell.Prelude

record Tup (a b : Type) : Type where
  constructor MkTup
  field exl : a ; exr : b
open Tup public

{-# COMPILE AGDA2HS Tup #-}

swap : Tup a b → Tup b a
swap = λ (MkTup x y) → MkTup y x

{-# COMPILE AGDA2HS swap #-}
