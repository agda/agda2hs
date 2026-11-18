open import Haskell.Prelude

private variable
    @0 n : Nat

data Vec (a : Set) : @0 Nat → Set where
    [] : Vec a 0
    _∷_ : a → Vec a n → Vec a (suc n)

{-# COMPILE AGDA2HS Vec to List #-}

-- The instance has no compilation pragma of its own, but it is used in
-- compiled code, so it needs a `to` pragma.
instance
  iEqVec : {{Eq a}} → Eq (Vec a n)
  iEqVec {a} ._==_ = eqList
    where
      eqList : Vec a n → Vec a n → Bool
      eqList [] [] = True
      eqList (x ∷ xs) (y ∷ ys) = x == y && eqList xs ys
      eqList _ _ = False

test : Bool
test = eqTest (1 ∷ 2 ∷ []) (1 ∷ 3 ∷ [])
  where
    eqTest : Vec Int 2 → Vec Int 2 → Bool
    eqTest x y = x == y

{-# COMPILE AGDA2HS test #-}
