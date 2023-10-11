-- Using a default method implementation for an instance declaration currently
-- requires a named definition or an anonymous `λ where` on the Agda side, so a
-- record is not allowed.

module Fail.Issue169-record where

open import Haskell.Prelude

record Identity (a : Set) : Set where
    field
        runIdentity : a
open Identity public

{-# COMPILE AGDA2HS Identity newtype #-}

showIdentity : ⦃ Show a ⦄ → Identity a → String
showIdentity record { runIdentity = id } = "Id < " ++ show id ++ " >"

{-# COMPILE AGDA2HS showIdentity #-}

instance
  iIdentityShow : ⦃ Show a ⦄ → Show (Identity a)
  iIdentityShow = record {Show₂ record {show = showIdentity}}

{-# COMPILE AGDA2HS iIdentityShow #-}
