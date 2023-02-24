module Fail.Issue146 where

open import Haskell.Prelude

record Wrap (a : Set) : Set where
  constructor MkWrap
  field wrapped : a
open Wrap public

{-# COMPILE AGDA2HS Wrap #-}

record Class (a : Set) : Set where
  field
    method : Wrap a → Wrap a
open Class ⦃...⦄ public

{-# COMPILE AGDA2HS Class class #-}

instance
  BoolClass : Class Bool
  BoolClass .method (MkWrap x) .wrapped = x

  {-# COMPILE AGDA2HS BoolClass #-}

