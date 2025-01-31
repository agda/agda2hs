module Haskell.Data.ByteString where

open import Haskell.Prelude

postulate
  ByteString : Type

  instance
    iEqByteString : Eq ByteString
