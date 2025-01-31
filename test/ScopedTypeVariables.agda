open import Haskell.Prelude

module ScopedTypeVariables (@0 x : Bool) where

-- We can encode explicit `forall` quantification by module parameters in Agda.
module _ {a : Type} {{_ : Eq a}} where
  foo : a → Bool
  foo x = it x == x
    where
      it : a -> a
      it = const x
{-# COMPILE AGDA2HS foo #-}

-- Type arguments should be compiled in the right order.
module _ {a b : Type} where
  bar : a → b → (b → b) → b
  bar x y f = baz y
    where
      baz : b → b
      baz z = f (f z)
{-# COMPILE AGDA2HS bar #-}

data D : Type where
  MakeD : (y : Bool) → @0 x ≡ y → D
{-# COMPILE AGDA2HS D #-}

mybool : Bool
mybool = False
{-# COMPILE AGDA2HS mybool #-}
