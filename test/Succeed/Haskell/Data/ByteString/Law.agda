module Haskell.Data.ByteString.Law where

open import Haskell.Prelude
open import Haskell.Law.Eq.Def
open import Haskell.Data.ByteString

postulate instance
  @0 iLawfulEqByteString : IsLawfulEq ByteString
