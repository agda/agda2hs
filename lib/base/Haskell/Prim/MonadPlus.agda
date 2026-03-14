module Haskell.Prim.MonadPlus where

open import Haskell.Prim
open import Haskell.Prim.Alternative
open import Haskell.Prim.Monad
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe


--------------------------------------------------------------------------------
-- MonadPlus

-- ** base
record MonadPlus (m : Type → Type) : Type₁ where
  field
    overlap ⦃ super₁ ⦄ : Alternative m
    overlap ⦃ super₂ ⦄ : Monad m
    mzero : m a
    mplus : m a → m a → m a

-- ** default
record DefaultMonadPlus (m : Type → Type) : Type₁ where
  field
    overlap ⦃ super₁ ⦄ : Alternative m
    overlap ⦃ super₂ ⦄ : Monad m
  
  mzero : m a
  mzero = empty

  mplus : m a → m a → m a
  mplus = _<|>_

-- ** export
open MonadPlus ⦃...⦄ public
{-# COMPILE AGDA2HS MonadPlus existing-class #-}

-- ** instances
instance
  open DefaultMonadPlus

  iDefaultMonadPlusList : DefaultMonadPlus List
  iDefaultMonadPlusList = record {}

  iMonadPlusList : MonadPlus List
  iMonadPlusList = record {DefaultMonadPlus iDefaultMonadPlusList}

  iDefaultMonadPlusMaybe : DefaultMonadPlus Maybe
  iDefaultMonadPlusMaybe = record {}

  iMonadPlusMaybe : MonadPlus Maybe
  iMonadPlusMaybe = record {DefaultMonadPlus iDefaultMonadPlusMaybe}
  
  iDefaultMonadPlusIO : DefaultMonadPlus IO
  iDefaultMonadPlusIO = record {}
  
  iMonadPlusIO : MonadPlus IO
  iMonadPlusIO = record {DefaultMonadPlus iDefaultMonadPlusIO}
