module Haskell.Data.ByteString where

open import Haskell.Prelude

postulate
  ByteString : Set

  instance
    iEqByteString : Eq ByteString
