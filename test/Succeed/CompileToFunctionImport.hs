module CompileToFunctionImport
  (test)
where

import CompileToFunctionTarget (target)
import Numeric.Natural (Natural)

test :: [Natural] -> Natural
test = target

