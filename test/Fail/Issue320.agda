module Fail.Issue320 where

import Haskell.Prelude

postulate ByteString : Set

record Hash (a : Set) : Set where
  constructor MakeHash
  field hashBytes : ByteString
open Hash public
{-# COMPILE AGDA2HS Hash newtype deriving (Generic, Show) #-}
