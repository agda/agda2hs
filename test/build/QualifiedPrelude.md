```haskell
module QualifiedPrelude where

import Numeric.Natural (Natural)
import qualified Prelude as Pre (foldr, (+), (.))

-- ** qualifying the Prelude

(+) :: Natural -> Natural -> Natural
x + y = x

comp ::
     (Natural -> Natural) -> (Natural -> Natural) -> Natural -> Natural
comp f g = (Pre..) f g

test :: Natural
test = (Pre.+) 0 (1 + 0)

testComp :: Natural
testComp = comp (+ 0) (\ section -> (Pre.+) section 1) 0

-- ** interplay with (qualified) default methods of existing class

testFoldr :: [Natural] -> Natural
testFoldr = Pre.foldr (\ _ x -> x) 0

-- ** re-qualifying the Prelude

retest :: Natural
retest = (Pre.+) 0 (1 + 0)

```
