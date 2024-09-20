```haskell
module Issue90 where

import Numeric.Natural (Natural)

good :: Natural
good = bar
  where
    foo :: Natural
    foo = 42
    bar :: Natural
    bar = foo

bad :: Natural
bad = bar
  where
    bar :: Natural
    bar = foo
    foo :: Natural
    foo = 42

good2 :: Natural
good2 = bar
  where
    foo :: Natural
    foo = 42 + x
      where
        x :: Natural
        x = 1
    bar :: Natural
    bar = foo + x
      where
        x :: Natural
        x = 2

bad2 :: Natural
bad2 = bar
  where
    bar :: Natural
    bar = foo + x
      where
        x :: Natural
        x = 2
    foo :: Natural
    foo = 42 + x
      where
        x :: Natural
        x = 1

test :: Bool -> Natural
test True = bar
  where
    foo :: Natural
    foo = 42 + ted
      where
        nes :: Natural
        nes = 1
        ted :: Natural
        ted = nes + 1
    bar :: Natural
    bar = foo
test False = bar
  where
    bar :: Natural
    bar = foo
    foo :: Natural
    foo = 42 + ted
      where
        ted :: Natural
        ted = nes + 1
        nes :: Natural
        nes = 1

```
