open import Haskell.Prelude

private variable
    @0 n : Nat

data Vec (a : Set) : @0 Nat → Set where
    [] : Vec a 0
    _∷_ : a → Vec a n → Vec a (suc n)

{-# COMPILE AGDA2HS Vec to List #-}

-- The instance for the compile-to type is compiled to the instance for the
-- target type, so no duplicate instance is generated. The compiled declaration
-- must match the one of the target instance, including the name of the local
-- `where` helper.
instance
  iEqVec : {{Eq a}} → Eq (Vec a n)
  iEqVec {a} ._==_ = eqList
    where
      eqList : Vec a n → Vec a n → Bool
      eqList [] [] = True
      eqList (x ∷ xs) (y ∷ ys) = x == y && eqList xs ys
      eqList _ _ = False

{-# COMPILE AGDA2HS iEqVec to iEqList #-}

test : Bool
test = eqTest (1 ∷ 2 ∷ []) (1 ∷ 3 ∷ [])
  where
    eqTest : Vec Int 2 → Vec Int 2 → Bool
    eqTest x y = x == y

{-# COMPILE AGDA2HS test #-}
