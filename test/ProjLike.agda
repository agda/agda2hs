{-# OPTIONS --projection-like #-}

module ProjLike where

open import Haskell.Prelude

module M (a : Type) where

  data Scope : Type where
    Empty : Scope
    Bind  : a → Scope → Scope
  
  {-# COMPILE AGDA2HS Scope #-}

  unbind : Scope → Scope
  unbind Empty      = Empty
  unbind (Bind _ s) = s

open M Nat public

test : Scope
test = unbind (Bind 1 (Bind 2 Empty))

{-# COMPILE AGDA2HS test #-}
