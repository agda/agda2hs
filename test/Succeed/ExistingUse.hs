module ExistingUse
  (useExistingImported)
where

import Existing (existingFun)

useExistingImported :: Int
useExistingImported = existingFun

