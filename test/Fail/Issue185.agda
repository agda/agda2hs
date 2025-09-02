module Fail.Issue185 where

open import Haskell.Prim using (Bool; True; Type)

record RecordTest : Type where
  no-eta-equality
  constructor MkRecord
  field
    aBool : Bool

  aBoolAsAFunction : Bool
  aBoolAsAFunction = aBool
open RecordTest public
{-# COMPILE AGDA2HS RecordTest newtype #-}
{-# COMPILE AGDA2HS aBoolAsAFunction #-}

test : Bool
test = aBoolAsAFunction (MkRecord True)
{-# COMPILE AGDA2HS test #-}
