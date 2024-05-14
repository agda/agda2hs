```haskell
module QualifiedModule where

data D = C

f :: D -> D
f C = C

g :: D
g = h
  where
    h :: D
    h = C

```
