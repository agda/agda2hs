
open import Haskell.Prelude
open import Issue324instance

test : Bool
test = not == id

{-# COMPILE AGDA2HS test #-}
