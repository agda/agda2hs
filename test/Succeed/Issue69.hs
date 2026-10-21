module Issue69
  (Map(..), size)
where

import Numeric.Natural (Natural)

data Map k a = Bin Natural k a (Map k a) (Map k a)
             | Tip

size :: Map k a -> Natural
size Tip = 0
size (Bin sz _ _ _ _) = sz

