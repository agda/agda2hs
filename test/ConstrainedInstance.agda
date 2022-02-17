
open import Haskell.Prelude

data D (a : Set) : Set where
  C : a → D a
{-# COMPILE AGDA2HS D #-}

instance
  iEqD : {{Eq a}} → Eq (D a)
  iEqD ._==_ (C x) (C y) = x == y
{-# COMPILE AGDA2HS iEqD #-}
