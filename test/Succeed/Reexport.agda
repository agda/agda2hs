module Reexport where

-- Reexport AgdaModule
open import Inlining public

-- Nothing is reexported on Haskell side -> dropped
open import ExportTransparentOnly public

-- Reexport HsModule
open import Haskell.Data.List public

-- Reexports inside nested modules are not supported (ignored)

module M where
  open import Importee public

open M public

module M2 where
  open import Test public
