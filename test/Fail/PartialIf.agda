module Fail.PartialIf where

open import Haskell.Prelude

if_partial : (flg : Bool) → (@0 {{ flg ≡ True }} → Nat) → (@0 {{ flg ≡ False }} → Nat) → Nat
if_partial = if_then_else_
{-# COMPILE AGDA2HS if_partial #-}
