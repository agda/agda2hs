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

-- To make output non-empty
data Dummy : Set where
  Dum : Dummy
{-# COMPILE AGDA2HS Dummy #-}
