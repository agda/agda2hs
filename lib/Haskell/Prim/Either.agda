
module Haskell.Prim.Either where

open import Haskell.Prim
open import Haskell.Prim.Bool

--------------------------------------------------
-- Either

data Either (a b : Type) : Type where
  Left  : a → Either a b
  Right : b → Either a b

either : (a → c) → (b → c) → Either a b → c
either f g (Left  x) = f x
either f g (Right y) = g y

testBool : (b : Bool) → Either (IsFalse b) (IsTrue b)
testBool False = Left  itsFalse
testBool True  = Right itsTrue
