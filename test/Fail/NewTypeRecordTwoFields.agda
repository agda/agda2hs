module Fail.NewTypeRecordTwoFields where

open import Haskell.Prelude

record Duo (a b : Type) : Type where
    constructor MkDuo
    field
        left : a
        right : b
open Duo public

{-# COMPILE AGDA2HS Duo newtype #-}

