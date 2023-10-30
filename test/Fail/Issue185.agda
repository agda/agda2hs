module Fail.Issue185 where

open import Agda.Builtin.Bool

record RecordTest : Set where
  constructor MkRecord
  field
    aBool : Bool

  aBoolAsAFunction : Bool
  aBoolAsAFunction = aBool
open RecordTest public
{-# COMPILE AGDA2HS RecordTest newtype #-}
{-# COMPILE AGDA2HS aBoolAsAFunction #-}

test : Bool
test = aBoolAsAFunction (MkRecord true)
{-# COMPILE AGDA2HS test #-}
