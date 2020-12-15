
module Haskell.Prim.Either where

open import Haskell.Prim

--------------------------------------------------
-- Either

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

either : (a → c) → (b → c) → Either a b → c
either f g (Left  x) = f x
either f g (Right y) = g y
