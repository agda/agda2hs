open import Haskell.Prelude

foo : Int
foo = 42

{-# COMPILE AGDA2HS foo #-}
