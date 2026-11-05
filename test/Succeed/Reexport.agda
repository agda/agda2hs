module Reexport where

-- Reexport AgdaModule
open import Inlining public

-- Nothing is reexported on Haskell side -> dropped
open import ExportTransparentOnly public

-- Reexport HsModule
open import Haskell.Data.List public

-- Reexport Prelude
open import Haskell.Prelude public

-- Reexport other PrimModule -> dropped
open import Haskell.Prim.Nat public

-- Preserve module qualifier
open import Importee as X public

-- Reexports inside nested modules are not supported (ignored)

module M where
  open import Importee public

open M public

module M2 where
  open import Test public
