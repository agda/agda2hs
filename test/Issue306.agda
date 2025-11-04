open import Haskell.Prelude

-- Unlike the tests in Fail/ related to issue #306, here we check that
-- instances in modules WITHOUT dot patterns can actually work (previously
-- threw __IMPOSSIBLE__)
module Issue306 where

record Foo (a b : Set) : Set where
  no-eta-equality
  field
    coe : a → b
open Foo public

module _ {a : Set} where
  instance
    foo : Foo a a
    foo .coe x = x

{-# COMPILE AGDA2HS Foo class #-}
{-# COMPILE AGDA2HS foo #-}
