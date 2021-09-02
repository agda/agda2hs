
open import Agda.Builtin.Nat

data Vec (a : Set) : {n : Nat} → Set where
  Nil : Vec a {0}
  Cons : {n : Nat} → a → Vec a {n} → Vec a {suc n}
{-# COMPILE AGDA2HS Vec #-}

mapV : {a b : Set} {n : Nat} (f : a → b) → Vec a {n} → Vec b {n}
mapV f Nil = Nil
mapV f (Cons x xs) = Cons (f x) (mapV f xs)
{-# COMPILE AGDA2HS mapV #-}

tailV : {a : Set} {n : Nat} → Vec a {suc n} → Vec a {n}
tailV (Cons x xs) = xs
{-# COMPILE AGDA2HS tailV #-}
