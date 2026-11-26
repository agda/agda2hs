open import Haskell.Prelude

data MyList (a : Set) : Set where
  Nil  : MyList a
  Cons : a → MyList a → MyList a

{-# COMPILE AGDA2HS MyList #-}

instance
  iEqMyList : {{Eq a}} → Eq (MyList a)
  iEqMyList {a} ._==_ = eqMyList
    where
      eqMyList : MyList a → MyList a → Bool
      eqMyList Nil Nil = True
      eqMyList (Cons x xs) (Cons y ys) = x == y && eqMyList xs ys
      eqMyList _ _ = False

{-# COMPILE AGDA2HS iEqMyList #-}
