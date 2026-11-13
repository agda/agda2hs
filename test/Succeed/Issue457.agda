module Issue457 where

open import Haskell.Prelude

usingMapM : Maybe (List Nat)
usingMapM = mapM pure []

{-# COMPILE AGDA2HS usingMapM #-}
