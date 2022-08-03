
module Fail.TupleType where

open import Haskell.Prelude

idT : ∀ {@0 as} → Tuple as → Tuple as
idT x = x

{-# COMPILE AGDA2HS idT #-}
