open import Haskell.Prelude

private variable
  @0 n : Nat

-- An unboxed record wrapping a natural number together with a proof that it is
-- below the bound. Its `Eq` instance just defers to the existing instance for
-- `Nat` instead of comparing the numbers from scratch.
record Fin (@0 n : Nat) : Type where
  constructor mkFin
  field
    value : Nat
    @0 proof : IsTrue (value < n)
open Fin public
{-# COMPILE AGDA2HS Fin unboxed #-}

instance
  iEqFin : Eq (Fin n)
  iEqFin ._==_ x y = value x == value y
{-# COMPILE AGDA2HS iEqFin to iEqNat #-}

test : Bool
test = x == y
  where
    x : Fin 10
    x = mkFin 3 IsTrue.itsTrue
    y : Fin 10
    y = mkFin 4 IsTrue.itsTrue
{-# COMPILE AGDA2HS test #-}
