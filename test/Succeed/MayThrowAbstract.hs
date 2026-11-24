module MayThrowAbstract
  (throwing)
where

import Control.Exception (assert)
import Numeric.Natural (Natural)

throwing :: Natural -> Natural
throwing x = assert (x == 0) x

