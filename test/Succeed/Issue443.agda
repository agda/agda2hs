-- See issue #443: postulates in a `where` block are compiled to a
-- runtime error.
module Issue443 where

open import Haskell.Prelude

test : ⊤
test = local
  where postulate local : ⊤

{-# COMPILE AGDA2HS test #-}
