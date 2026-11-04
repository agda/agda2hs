{-# OPTIONS --erasure #-}
module Issue454Record where

open import Haskell.Prelude

record Example (a : Type) : Type where
  no-eta-equality
  field
    fun : a → a

open Example public

{-# COMPILE AGDA2HS Example #-}
