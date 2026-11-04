module PreludeClashCon where

open import Haskell.Prim using (Type)

data T : Type where
  Just : T

{-# COMPILE AGDA2HS T #-}
