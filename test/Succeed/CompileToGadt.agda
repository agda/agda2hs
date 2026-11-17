module CompileToGadt where

open import Haskell.Prelude
open import CompileToGadtTarget using (Res)

-- A datatype compiled to a target that uses GADT syntax.
data Src (a : Type) : Type where
  MkRes : a → Src a

{-# COMPILE AGDA2HS Src to Res #-}

toRes : a → Src a
toRes = MkRes

{-# COMPILE AGDA2HS toRes #-}
