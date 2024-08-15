```haskell
{-# LANGUAGE TypeOperators #-}

module TypeOperators where

import Numeric.Natural (Natural)

type (:++:) = Either

mx :: (:++:) Bool Natural
mx = Left True

type (++++) = Either

mx' :: (++++) Bool Natural
mx' = Left True

data (****) a b = (:****) a b

cross :: (****) Bool Natural
cross = True :**** 1

```
