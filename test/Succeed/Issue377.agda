module Issue377 where

open import Haskell.Prelude
open import Haskell.Data.Maybe

test : Integer
test = fromMaybe 0 (Just 12)

{-# COMPILE AGDA2HS test #-}
