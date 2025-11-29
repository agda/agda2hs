{-# FOREIGN AGDA2HS
-- ** common qualification
#-}

import Haskell.Prelude as Common
import Importee as Common
  using (foo)
import Importee as Common
  using (anotherFoo)

foos : Common.Int
foos = Common.foo Common.+ Common.anotherFoo
{-# COMPILE AGDA2HS foos #-}
