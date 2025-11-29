{-# LANGUAGE TypeOperators #-}

module TypeOperatorImport where

import TypeOperatorExport ((&&&), type (***)((:*:)), type (<))

test1 :: (<) () Bool
test1 = ()

test2 :: Bool -> Bool -> (***) () Bool
test2 b1 b2 = ((() :*:) . not) (b1 &&& b2)

