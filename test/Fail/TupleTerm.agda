
module Fail.TupleTerm where

open import Haskell.Prelude

pair2trip : a → b × c → a × b × c
pair2trip x xs = x ; xs

{-# COMPILE AGDA2HS pair2trip #-}
