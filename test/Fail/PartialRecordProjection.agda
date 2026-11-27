module PartialRecordProjection where

open import Haskell.Prelude
open import PartialRecord

getHidden : PartiallyExported → Int
getHidden = PartiallyExported.hiddenField
{-# COMPILE AGDA2HS getHidden #-}
