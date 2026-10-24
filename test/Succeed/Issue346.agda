-- Note: the output for this module is currently empty which is WRONG
-- Once https://github.com/agda/agda/issues/8092 is fixed and agda2hs is
-- updated to use the fixed version of Agda, the output for this test
-- case should be updated.

data D : Set
{-# COMPILE AGDA2HS D #-}
data D where  DC : D

record R : Set
{-# COMPILE AGDA2HS R #-}
record R where constructor RC

f : D → R
{-# COMPILE AGDA2HS f #-}
f DC = RC

-- To make output non-empty
data Dummy : Set where
  Dum : Dummy
{-# COMPILE AGDA2HS Dummy #-}
