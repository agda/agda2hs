
open import Haskell.Prelude

{- Old style using implicit arguments (no longer supported)
data Vec (a : Type) : {n : Nat} → Type where
  Nil : Vec a {0}
  Cons : {n : Nat} → a → Vec a {n} → Vec a {suc n}
{-# COMPILE AGDA2HS Vec #-}

mapV : {a b : Type} {n : Nat} (f : a → b) → Vec a {n} → Vec b {n}
mapV f Nil = Nil
mapV f (Cons x xs) = Cons (f x) (mapV f xs)
{-# COMPILE AGDA2HS mapV #-}

tailV : {a : Type} {n : Nat} → Vec a {suc n} → Vec a {n}
tailV (Cons x xs) = xs
{-# COMPILE AGDA2HS tailV #-}
-}

-- New style using erasure instead of implicit arguments
data Vec (a : Type) : (@0 n : Nat) → Type where
  Nil : Vec a 0
  Cons : {@0 n : Nat} → a → Vec a n → Vec a (suc n)
{-# COMPILE AGDA2HS Vec #-}

mapV : {a b : Type} {@0 n : Nat} (f : a → b) → Vec a n → Vec b n
mapV f Nil = Nil
mapV f (Cons x xs) = Cons (f x) (mapV f xs)
{-# COMPILE AGDA2HS mapV #-}

tailV : {a : Type} {@0 n : Nat} → Vec a (suc n) → Vec a n
tailV (Cons x xs) = xs
{-# COMPILE AGDA2HS tailV #-}
