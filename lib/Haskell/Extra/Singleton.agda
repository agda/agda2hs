module Haskell.Extra.Singleton where

open import Haskell.Prelude

data Singleton (a : Set) : @0 a → Set where
  MkSingl : ∀ x → Singleton a x

{-# COMPILE AGDA2HS Singleton unboxed #-}

pureSingl : {a : Set} (x : a) → Singleton a x
pureSingl = MkSingl

{-# COMPILE AGDA2HS pureSingl inline #-}

fmapSingl
  : {a b : Set} (f : a → b) {@0 x : a}
  → Singleton a x
  → Singleton b (f x)
fmapSingl f (MkSingl x) = MkSingl (f x)

{-# COMPILE AGDA2HS fmapSingl inline #-}
