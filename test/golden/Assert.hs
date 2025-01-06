module Assert where

import Control.Exception (assert)
import Numeric.Natural (Natural)

subtractChecked :: Natural -> Natural -> Natural
subtractChecked x y = assert (not (x < y)) (x - y)

