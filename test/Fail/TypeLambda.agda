
module Fail.TypeLambda where

open import Haskell.Prelude

foo : (f : (Type → Type) → Type) (x : f (λ y → Nat)) (y : f List) → Nat
foo f x y = 42

{-# COMPILE AGDA2HS foo #-}
