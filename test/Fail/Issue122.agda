-- See issue #122: local modules with definitions of the same name
-- produce clashing top-level definitions in the generated Haskell code.
module Issue122 where

open import Haskell.Prelude

module M1 where

  foo : Int
  foo = 21

  {-# COMPILE AGDA2HS foo #-}

module M2 where

  foo : Int
  foo = 21

  {-# COMPILE AGDA2HS foo #-}

bar : Int
bar = M1.foo + M2.foo

{-# COMPILE AGDA2HS bar #-}
