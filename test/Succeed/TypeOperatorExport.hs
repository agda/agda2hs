{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeOperators #-}

module TypeOperatorExport
  (type (<), type (***)(..), (&&&))
where

type (<) a b = a

data (***) a b = (:*:) a b

(&&&) :: Bool -> Bool -> Bool
False &&& _ = False
_ &&& b2 = b2

