module Haskell.Prim.Alternative where

open import Haskell.Prim
open import Haskell.Prim.Applicative
  renaming (module Instances to ApplicativeInstances)
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.String


--------------------------------------------------------------------------------
-- Alternative

-- ** base
record Alternative (f : Type → Type) : Type₁ where
  infixl 3 _<|>_
  field
    empty : f a
    _<|>_ : f a → f a → f a
    overlap ⦃ super ⦄ : Applicative f

-- ** export
open Alternative ⦃...⦄ public
{-# COMPILE AGDA2HS Alternative existing-class #-}

-- ** instances
module Instances where
  instance
    iAlternativeList : Alternative List
    iAlternativeList .empty = []
    iAlternativeList ._<|>_ = _++_

    iAlternativeMaybe : Alternative Maybe
    iAlternativeMaybe .empty = Nothing
    iAlternativeMaybe ._<|>_ (Just x) _ = Just x
    iAlternativeMaybe ._<|>_ Nothing  y = y

    iAlternativeIO : Alternative IO
    iAlternativeIO .empty = failIO "mzero"
    iAlternativeIO ._<|>_ = mplusIO
open Instances public
