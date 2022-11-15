open import Haskell.Prelude

data T (n : Nat) : Set where
  MkT : T n
{-# COMPILE AGDA2HS T #-}
