module CompileToDataParams where

open import Haskell.Prelude

-- The parameters are bound by the datatypes, so they must be compared by
-- identity rather than up to renaming. Here the constructor argument types
-- mention the parameters in a different order, so `Bar` cannot be compiled to
-- `Foo` even though the two argument types are equal up to the renaming
-- `a ↦ b`.
data Foo (a b : Type) : Type where
  C : b → a → Foo a b
{-# COMPILE AGDA2HS Foo #-}

data Bar (a b : Type) : Type where
  D : a → b → Bar a b
{-# COMPILE AGDA2HS Bar to Foo #-}
