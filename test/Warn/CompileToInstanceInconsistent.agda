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
