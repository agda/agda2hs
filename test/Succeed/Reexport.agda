module Reexport where

open import TransparentFun public
open import Inlining public

module M where
  open import Importee public

open M public

module M2 where
  open import Test public
