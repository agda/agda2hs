module PartialRecord where

open import Haskell.Prelude

-- Only `exportedField` is opened publicly, so it is compiled to a Haskell
-- selector while `hiddenField` is not.
record PartiallyExported : Set where
  no-eta-equality
  field
    exportedField : Int
    hiddenField : Int
open PartiallyExported public using (exportedField)

{-# COMPILE AGDA2HS PartiallyExported #-}
