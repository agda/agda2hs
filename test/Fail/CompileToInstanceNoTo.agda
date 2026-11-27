open import Haskell.Prelude

private variable
    @0 n : Nat

data Vec (a : Set) : @0 Nat → Set where
    [] : Vec a 0
    _∷_ : a → Vec a n → Vec a (suc n)

{-# COMPILE AGDA2HS Vec to List #-}

instance
  iEqVec : {{Eq a}} → Eq (Vec a n)
  iEqVec {a} ._==_ = eqList
    where
      eqList : Vec a n → Vec a n → Bool
      eqList [] [] = True
      eqList (x ∷ xs) (y ∷ ys) = x == y && eqList xs ys
      eqList _ _ = False

-- The instance is compiled, but it is for a type with a compile-to pragma, so
-- it needs a `to` pragma as well.
{-# COMPILE AGDA2HS iEqVec #-}
