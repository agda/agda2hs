
data Nat : Set where
  Zero : Nat
  Suc  : Nat → Nat
{-# COMPILE AGDA2HS Nat #-}

Nat' = Nat
{-# COMPILE AGDA2HS Nat' #-}

data List (a : Set) : Set where
  Nil : List a
  Cons : a → List a → List a
{-# COMPILE AGDA2HS List #-}

List' : Set → Set
List' a = List a
{-# COMPILE AGDA2HS List' #-}

NatList = List Nat
{-# COMPILE AGDA2HS NatList #-}

ListList : Set → Set
ListList a = List (List a)
{-# COMPILE AGDA2HS ListList #-}
