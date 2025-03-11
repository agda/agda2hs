```haskell
module RequalifiedImports where

import OtherImportee (OtherFoo(MkFoo))
import QualifiedImportee ()
import qualified QualifiedImportee as A (Foo, Fooable(defaultFoo, doTheFoo), foo, (!#))

-- ** conflicting imports are all replaced with the "smallest" qualifier
--   * the characters are ordered based on their ASCII value (i.e. capitals first)
--   * the order of the imports in the file does not matter
--   * the scope-checker has already replaced previous definitions in the file

requalBar :: Int
requalBar = A.foo

requalBaz :: Int
requalBaz = (A.!#) 2 2

requalFooable :: A.Foo
requalFooable = A.doTheFoo

requalDefaultBar :: A.Foo
requalDefaultBar = A.defaultFoo

-- ** qualifying an open'ed module has no effect

type T = Int

otherFoo :: OtherFoo
otherFoo = MkFoo

```
