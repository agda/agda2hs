{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Floating where

open import Haskell.Prim
open import Haskell.Prim.Double
open import Haskell.Prim.Fractional

--------------------------------------------------
-- Floating

record Floating (a : Type) : Type₁ where
  infixr 8 _**_   -- Haskell: infixr 8 **
  field
    overlap ⦃ fractional ⦄ : Fractional a

    pi                   : a
    exp log sqrt         : a → a
    _**_                 : a → a → a
    logBase              : a → a → a
    sin cos tan          : a → a
    asin acos atan       : a → a
    sinh cosh tanh       : a → a
    asinh acosh atanh    : a → a
open Floating ⦃...⦄ public hiding (fractional)

{-# COMPILE AGDA2HS Floating existing-class #-}

instance
  postulate iFloatingDouble : Floating Double
