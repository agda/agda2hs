module PrivateRecordFields where

open import Haskell.Prelude

-- The record module is not opened publicly, so the field is not exported to
-- Haskell and the type only exports its constructor.
record Secret : Set where
  no-eta-equality
  pattern
  field
    hidden : Int

{-# COMPILE AGDA2HS Secret #-}

mkSecret : Int → Secret
mkSecret x = record { hidden = x }
{-# COMPILE AGDA2HS mkSecret #-}

getSecret : Secret → Int
getSecret (record { hidden = x }) = x
{-# COMPILE AGDA2HS getSecret #-}
