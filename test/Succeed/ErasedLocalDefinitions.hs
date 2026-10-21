module ErasedLocalDefinitions
  (f)
where

f :: Bool -> Bool
f m = g m
  where
    g :: Bool -> Bool
    g m = m

