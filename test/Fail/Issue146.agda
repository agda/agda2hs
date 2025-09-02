module Fail.Issue146 where

open import Haskell.Prelude

record Wrap (a : Type) : Type where
  no-eta-equality
  constructor MkWrap
  field wrapped : a
open Wrap public

{-# COMPILE AGDA2HS Wrap #-}

record Class (a : Type) : Type where
  field
    method : a → Wrap a
open Class ⦃...⦄ public

{-# COMPILE AGDA2HS Class class #-}

instance
  BoolClass : Class Bool
  BoolClass .method x .wrapped = x

  {-# COMPILE AGDA2HS BoolClass #-}

