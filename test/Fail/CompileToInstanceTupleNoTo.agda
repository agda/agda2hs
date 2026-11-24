open import Haskell.Prelude

record Pair (a b : Type) : Type where
  constructor _,_
  field
    fst : a
    snd : b
open Pair public
{-# COMPILE AGDA2HS Pair tuple #-}

instance
  iEqPair : {{Eq a}} → {{Eq b}} → Eq (Pair a b)
  iEqPair ._==_ (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ && y₁ == y₂

-- The instance is compiled, but it is for a tuple record, so it must also have
-- a `to` pragma pointing to the instance for the corresponding tuple type.
{-# COMPILE AGDA2HS iEqPair #-}
