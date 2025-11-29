
module Issue65 where

open import Haskell.Prelude

yeet : (c : Bool) → (@0 {{c ≡ True}} → a) → (@0 {{c ≡ False}} → a) → a
yeet False x y = y {{refl}}
yeet True  x y = x {{refl}}
{-# COMPILE AGDA2HS yeet #-}

-- The branches start with instance lambdas that should be dropped.
xx : Int
xx = yeet True 1 2
{-# COMPILE AGDA2HS xx #-}
