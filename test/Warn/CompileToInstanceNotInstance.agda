open import Haskell.Prelude
open import Vec

private variable
    @0 n : Nat

instance
  iEqVec : {{Eq a}} → Eq (Vec a n)
  iEqVec {a} ._==_ = eqList
    where
      eqList : Vec a n → Vec a n → Bool
      eqList [] [] = True
      eqList (x ∷ xs) (y ∷ ys) = x == y && eqList xs ys

-- `map` is a function, not an instance, so the target cannot be used.
{-# COMPILE AGDA2HS iEqVec to map #-}
