module PreludeClashType where

open import Haskell.Prim using (Type)

data ReadS : Type where
  MkReadS : ReadS

{-# COMPILE AGDA2HS ReadS #-}
