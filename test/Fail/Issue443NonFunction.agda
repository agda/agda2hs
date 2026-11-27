-- See issue #443: declarations other than functions and postulates are
-- not supported in `where` blocks.
module Issue443NonFunction where

open import Haskell.Prelude

test : ⊤
test = tt
  where
    record Foo : Set where
      field x : ⊤

{-# COMPILE AGDA2HS test #-}
