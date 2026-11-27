module Issue394
  (test)
where

import Data.ByteString (ByteString)

test :: ByteString -> ByteString -> Bool
test x y = x == y

