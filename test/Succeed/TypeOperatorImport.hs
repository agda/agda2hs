{-# LANGUAGE TypeOperators #-}

module TypeOperatorImport
  (test1, test2)
where

import TypeOperatorExport ((&&&), type (***)((:*:)), type (<))

test1 :: (<) () Bool
test1 = ()

test2 :: Bool -> Bool -> (***) () Bool
test2 b1 b2 = ((() :*:) . not) (b1 &&& b2)

