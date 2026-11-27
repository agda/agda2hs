module Issue457
  (usingMapM)
where

import Numeric.Natural (Natural)

usingMapM :: Maybe [Natural]
usingMapM = mapM pure []

