```haskell
module Issue377 where

import Data.Maybe (fromMaybe)

test :: Integer
test = fromMaybe 0 (Just 12)

```
