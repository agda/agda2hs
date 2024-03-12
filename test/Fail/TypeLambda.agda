
module Fail.TypeLambda where

open import Haskell.Prelude

foo : (f : (Set → Set) → Set) (x : f (λ y → Nat)) (y : f List) → Nat
foo f x y = 42

{-# COMPILE AGDA2HS foo #-}
