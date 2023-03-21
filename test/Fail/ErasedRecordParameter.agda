-- c.f. Issue #145, this is the record variant
module Fail.ErasedRecordParameter where

record Ok (@0 a : Set) : Set where
  constructor Thing
  field unThing : a
open Ok public
{-# COMPILE AGDA2HS Ok #-}
