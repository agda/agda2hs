module ProjLike where

open import Haskell.Prelude

module M (a : Set) where

  data Scope : Set where
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
