module PartialRecordUse where

open import Haskell.Prelude
open import PartialRecord

getExported : PartiallyExported → Int
getExported = exportedField
{-# COMPILE AGDA2HS getExported #-}
