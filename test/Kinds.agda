module Kinds where

open import Haskell.Prelude

record ReaderT (r : Set) (m : Set → Set) (a  : Set) : Set where
  constructor RdrT
  field runReaderT : r → m a
open ReaderT public

{-# COMPILE AGDA2HS ReaderT #-}

data Kleisli (m : Set → Set) (a b : Set) : Set where
  K : (a → m b) → Kleisli m a b

{-# COMPILE AGDA2HS Kleisli #-}

