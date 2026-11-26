open import Haskell.Prelude
open import Vec

private variable
    @0 n : Nat

-- The instance is consistent with `iEqVec` on the cases it defines, but it is
-- missing the catch-all clause of the target instance, so agda2hs warns that it
-- could not check the two instances for equality.
instance
  iEqVec : {{Eq a}} → Eq (Vec a n)
  iEqVec {a} ._==_ = eqList
    where
      eqList : Vec a n → Vec a n → Bool
      eqList [] [] = True
      eqList (x ∷ xs) (y ∷ ys) = x == y || eqList xs ys

{-# COMPILE AGDA2HS iEqVec to iEqList #-}

data Pair (a b : Type) : Type where
  MkPair : a → b → Pair a b
{-# COMPILE AGDA2HS Pair #-}

record R (a b : Type) : Type where
  constructor mkR
  field unr : Pair a b
open R public
{-# COMPILE AGDA2HS R unboxed #-}

instance
  iEqPair : {{Eq a}} → {{Eq b}} → Eq (Pair a b)
  iEqPair ._==_ (MkPair x y) (MkPair u v) = x == u && y == v
{-# COMPILE AGDA2HS iEqPair #-}

-- The instance head mentions the type variables in a different order than the
-- context and than the target instance. The implicitly quantified variables
-- must be renamed consistently across the whole instance, so the two instances
-- are not alpha-equivalent and agda2hs warns.
instance
  iEqR : {{Eq c}} → {{Eq d}} → Eq (R d c)
  iEqR ._==_ x y = unr x == unr y
{-# COMPILE AGDA2HS iEqR to iEqPair #-}
