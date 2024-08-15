module Haskell.Extra.Singleton where

open import Haskell.Prelude hiding (pure; _<*>_)

data Singleton (a : Set) : @0 a → Set where
  MkSingl : ∀ x → Singleton a x
{-# COMPILE AGDA2HS Singleton unboxed #-}

module Idiom where

  pure : {a : Set} (x : a) → Singleton a x
  pure x = MkSingl x
  {-# COMPILE AGDA2HS pure inline #-}

  _<*>_ : {a b : Set} {@0 f : a → b} {@0 x : a}
        → Singleton (a → b) f → Singleton a x → Singleton b (f x)
  MkSingl f <*> MkSingl x = MkSingl (f x)
  {-# COMPILE AGDA2HS _<*>_ inline #-}

open Idiom public renaming (pure to pureSingl; _<*>_ to apSingl)

fmapSingl
  : {a b : Set} (f : a → b) {@0 x : a}
  → Singleton a x
  → Singleton b (f x)
fmapSingl f (MkSingl x) = MkSingl (f x)
{-# COMPILE AGDA2HS fmapSingl inline #-}

