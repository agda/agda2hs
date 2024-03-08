```haskell
module ErasedTypeArguments where

import Numeric.Natural (Natural)

data Σ' a b = (:^:){proj₁ :: a, proj₂ :: b}

test :: Natural -> Σ' Natural ()
test n = n :^: ()

newtype Id f = MkId f

```
