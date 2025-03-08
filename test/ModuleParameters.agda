{-# OPTIONS --no-projection-like #-}
open import Haskell.Prelude hiding (a)

module ModuleParameters
  (@0 name : Type)
  (p : @0 name → Type) where

data Scope : Type where
  Empty : Scope
  Bind  : (@0 x : name) → p x → Scope → Scope
{-# COMPILE AGDA2HS Scope #-}

unbind : Scope → Scope
unbind Empty = Empty
unbind (Bind _ _ s) = s
{-# COMPILE AGDA2HS unbind #-}

module _ {a : Type} where
  thing : a → a
  thing x = y
    where y : a
          y = x
  {-# COMPILE AGDA2HS thing #-}

  stuff : a → Scope → a
  stuff x Empty = x
  stuff x (Bind _ _ _) = x
  {-# COMPILE AGDA2HS stuff #-}

  module _ {b : Type} where
    more : b → a → Scope → Scope
    more _ _ Empty = Empty
    more _ _ (Bind _ _ s) = s
    {-# COMPILE AGDA2HS more #-}
