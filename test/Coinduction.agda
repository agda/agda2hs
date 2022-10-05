{-# OPTIONS --sized-types #-}

module Coinduction where

open import Haskell.Prelude
open import Haskell.Prim.Thunk

data Colist (a : Set) {i : Size} : Set where
  Nil  : Colist a
  Cons : a -> Thunk (λ {j} → Colist a {j}) i -> Colist a {i}

{-# COMPILE AGDA2HS Colist #-}

repeater : ∀ {a i} → a → Colist a {i}
repeater x = Cons x λ where .force → repeater x

{-# COMPILE AGDA2HS repeater #-}
