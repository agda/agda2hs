-- Regression test for #346: a datatype declared before its definition must
-- still be compiled to Haskell.

data D : Set
{-# COMPILE AGDA2HS D #-}
data D where  DC : D

record R : Set
{-# COMPILE AGDA2HS R #-}
record R where
  no-eta-equality
  constructor RC

f : D → R
{-# COMPILE AGDA2HS f #-}
f DC = RC
