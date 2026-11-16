module Existing
  (existingFun, ExistingData(..), ExistingClass(..), ExistingType, ord, useExisting)
where

import Data.Char (ord)

existingFun :: Int
existingFun = 42

data ExistingData = MkExistingData Int

class ExistingClass a where
  existingMethod :: a -> Int

type ExistingType = Int

useExisting :: Int -> Int
useExisting x = existingFun + x

