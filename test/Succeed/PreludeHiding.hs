module PreludeHiding
  (fromIntegral)
where

import Prelude hiding (fromIntegral)

fromIntegral :: Int -> Int
fromIntegral x = x

