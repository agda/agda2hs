module Fail.Issue223 where

open import Haskell.Prim using (Type)

data Void : Type where
{-# COMPILE AGDA2HS Void #-}

test : {a : Type} → Void → a
test ()
{-# COMPILE AGDA2HS test #-}
