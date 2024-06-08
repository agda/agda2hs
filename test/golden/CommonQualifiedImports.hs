module CommonQualifiedImports where

import qualified Importee as Common (foo)
import qualified SecondImportee as Common (anotherFoo)
import qualified Prelude as Common (Int, (+))

-- ** common qualification

foos :: Common.Int
foos = (Common.+) Common.foo Common.anotherFoo
