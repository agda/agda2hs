{-# OPTIONS --erasure #-}
module Issue454Import where

open import Haskell.Prelude
open import Issue454Record

fExample : {a : Type} → a → a
fExample a = a
{-# COMPILE AGDA2HS fExample #-}

example2 : (a : Type) → Example a
example2 a = record { fun = fExample }
{-# COMPILE AGDA2HS example2 #-}
