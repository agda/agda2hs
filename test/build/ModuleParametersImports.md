```haskell
module ModuleParametersImports where

import qualified ModuleParameters (Scope(Bind, Empty), unbind)
import Numeric.Natural (Natural)

scope :: ModuleParameters.Scope Natural
scope
  = ModuleParameters.unbind
      (ModuleParameters.Bind 3
         (ModuleParameters.Bind 2 ModuleParameters.Empty))

```
