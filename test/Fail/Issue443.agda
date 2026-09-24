open import Haskell.Prelude

module Fail.Issue443 where

test : ⊤
test = local
  where postulate local : ⊤

{-# COMPILE AGDA2HS test #-}
