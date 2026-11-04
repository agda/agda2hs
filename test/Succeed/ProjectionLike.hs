module ProjectionLike
  (R(..), foo)
where

data R = R{fld :: Int}

foo :: R -> Int
foo x = fld x

