module File2 where

open import Haskell.Prelude

open import File1

bar : Vec a 0
bar = foo
{-# COMPILE AGDA2HS bar #-}

num' : Nat
num' = num
{-# COMPILE AGDA2HS num' #-}

first : ∀ {@0 n} {a : Type} → Vec a (suc n) → a
first (x ∷ _) = x
{-# COMPILE AGDA2HS first #-}
