open import Haskell.Prelude

-- A tuple record is compiled to a Haskell pair. An `Eq` instance for it is
-- therefore compiled to the existing instance for pairs, so no duplicate
-- instance is generated.
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
{-# COMPILE AGDA2HS iEqPair to iEqTuple₂ #-}

test : Bool
test = xy == zw
  where
    xy : Pair Int Int
    xy = 1 , 2
    zw : Pair Int Int
    zw = 1 , 3
{-# COMPILE AGDA2HS test #-}
