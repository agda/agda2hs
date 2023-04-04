module Fail.NewTypeRecordTwoFields where

open import Haskell.Prelude

record Duo (a b : Set) : Set where
    constructor MkDuo
    field
        left : a
        right : b
open Duo public

{-# COMPILE AGDA2HS Duo newtype #-}

