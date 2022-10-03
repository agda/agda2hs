module ScopedTypeVariables where

open import Haskell.Prelude

-- We can encode explicit `forall` quantification by module parameters in Agda.
module _ {a : Set} {{_ : Eq a}} where
  foo : a → Bool
  foo x = it x == x
    where
      it : a -> a
      it = const x
{-# COMPILE AGDA2HS foo #-}

-- Type arguments should be compiled in the right order.
module _ {a b : Set} where
  bar : a → b → (b → b) → b
  bar x y f = baz y
    where
      baz : b → b
      baz z = f (f z)
{-# COMPILE AGDA2HS bar #-}
