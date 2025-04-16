module Issue394 where

import Data.ByteString (ByteString)

test :: ByteString -> ByteString -> Bool
test x y = x == y

