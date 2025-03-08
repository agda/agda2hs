-- c.f. Issue #145, this is the record variant
module Fail.ErasedRecordParameter where

open import Haskell.Prim using (Type)

record Ok (@0 a : Type) : Type where
  constructor Thing
  field unThing : a
open Ok public
{-# COMPILE AGDA2HS Ok #-}
