module Kinds where

open import Haskell.Prelude

record ReaderT (r : Type) (m : Type → Type) (a  : Type) : Type where
  no-eta-equality
  constructor RdrT
  field runReaderT : r → m a
open ReaderT public

{-# COMPILE AGDA2HS ReaderT #-}

data Kleisli (m : Type → Type) (a b : Type) : Type where
  K : (a → m b) → Kleisli m a b

{-# COMPILE AGDA2HS Kleisli #-}

