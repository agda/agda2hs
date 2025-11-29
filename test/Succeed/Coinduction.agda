{-# OPTIONS --sized-types #-}

module Coinduction where

open import Haskell.Prelude
open import Haskell.Prim.Thunk

data Colist (a : Type) (@0 i : Size) : Type where
  Nil  : Colist a i
  Cons : a -> Thunk (Colist a) i -> Colist a i

{-# COMPILE AGDA2HS Colist #-}

repeater : ∀ {a i} → a → Colist a i
repeater x = Cons x λ where .force → repeater x

{-# COMPILE AGDA2HS repeater #-}
