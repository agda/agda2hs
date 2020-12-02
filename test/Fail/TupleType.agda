
module Fail.TupleType where

open import Haskell.Prelude

idT : ∀ {as} → Tuple as → Tuple as
idT x = x

{-# COMPILE AGDA2HS idT #-}
