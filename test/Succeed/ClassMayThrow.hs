module ClassMayThrow
  (Checked(..))
where

import Control.Exception (assert)
import Numeric.Natural (Natural)

class Checked a where
    checked :: a -> a

instance Checked Natural where
    checked x = assert (x == 0) x

