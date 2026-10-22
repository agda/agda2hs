module RequalifiedImports
  (requalBar, requalBaz, requalFooable, requalDefaultBar, T, otherFoo)
where

import OtherImportee (OtherFoo(MkFoo))
import QualifiedImportee ()
import qualified QualifiedImportee as C (Foo, Fooable(defaultFoo, doTheFoo), foo, (!#))

-- ** conflicting imports are all replaced with the "smallest" qualifier
--   * the characters are ordered based on their ASCII value (i.e. capitals first)
--   * the order of the imports in the file does not matter
--   * the scope-checker has already replaced previous definitions in the file

requalBar :: Int
requalBar = C.foo

requalBaz :: Int
requalBaz = (C.!#) 2 2

requalFooable :: C.Foo
requalFooable = C.doTheFoo

requalDefaultBar :: C.Foo
requalDefaultBar = C.defaultFoo

-- ** qualifying an open'ed module has no effect

type T = Int

otherFoo :: OtherFoo
otherFoo = MkFoo

