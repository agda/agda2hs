
module Issue65 where

open import Haskell.Prelude

yeet : (c : Bool) → ({{c ≡ true}} → a) → ({{c ≡ false}} → a) → a
yeet false x y = y {{refl}}
yeet true  x y = x {{refl}}
{-# COMPILE AGDA2HS yeet #-}

-- The branches start with instance lambdas that should be dropped.
xx : Int
xx = yeet true 1 2
{-# COMPILE AGDA2HS xx #-}
