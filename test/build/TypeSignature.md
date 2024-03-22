```haskell
module TypeSignature where

import Numeric.Natural (Natural)

five :: Natural
five = (id :: Natural -> Natural) 5

```
