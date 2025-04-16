```haskell
module CommonQualifiedImports where

import qualified Importee as Common (foo)
import qualified Prelude as Common (Int, Num((+)))
import qualified SecondImportee as Common (anotherFoo)

-- ** common qualification

foos :: Common.Int
foos = (Common.+) Common.foo Common.anotherFoo

```
