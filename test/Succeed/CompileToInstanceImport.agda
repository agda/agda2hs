{-# OPTIONS --warning=noUnreachableClauses #-}

open import Haskell.Prelude
open import CompileToInstanceTarget

private variable
    @0 n : Nat

data Vec (a : Set) : @0 Nat → Set where
    Nil  : Vec a 0
    Cons : a → Vec a n → Vec a (suc n)

{-# COMPILE AGDA2HS Vec to MyList #-}

-- The target instance lives in another module, so its compiled declaration can
-- only be computed in the context of that module.
instance
  iEqVec : {{Eq a}} → Eq (Vec a n)
  iEqVec {a} ._==_ = eqMyList
    where
      eqMyList : Vec a n → Vec a n → Bool
      eqMyList Nil Nil = True
      eqMyList (Cons x xs) (Cons y ys) = x == y && eqMyList xs ys
      eqMyList _ _ = False

{-# COMPILE AGDA2HS iEqVec to iEqMyList #-}

test : Bool
test = eqTest (Cons 1 (Cons 2 Nil)) (Cons 1 (Cons 3 Nil))
  where
    eqTest : Vec Int 2 → Vec Int 2 → Bool
    eqTest x y = x == y

{-# COMPILE AGDA2HS test #-}
