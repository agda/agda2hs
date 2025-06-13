```haskell
{-# LANGUAGE TypeOperators #-}

module TypeOperatorExport where

type (<) a b = a

data (***) a b = (:*:) a b

(&&&) :: Bool -> Bool -> Bool
False &&& _ = False
_ &&& b2 = b2

```
