module Vec where

open import Haskell.Prelude

private variable
    @0 n : Nat

data Vec (a : Set) : @0 Nat → Set where
    [] : Vec a 0
    _∷_ : a → Vec a n → Vec a (suc n)

{-# COMPILE AGDA2HS Vec to List #-}
