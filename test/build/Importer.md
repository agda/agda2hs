```haskell
module Importer where

import Importee (Foo(MkFoo), Fooable(defaultFoo, doTheFoo), foo, (!#))
import Numeric.Natural (Natural)
import SecondImportee (anotherFoo)

-- ** simple imports (possibly with transitive dependencies)

bar :: Int
bar = foo

anotherBar :: Int
anotherBar = anotherFoo

baz :: Int
baz = 21 !# 21

mkFoo :: Foo
mkFoo = MkFoo

fooable :: Foo
fooable = doTheFoo

-- ** interplay with class default methods

defaultBar :: Foo
defaultBar = defaultFoo

-- ** interplay with methods of existing class

testFoldMap :: [Natural] -> [Natural]
testFoldMap = foldMap (:) []

-- ** interplay with default methods of existing class

testFoldr :: [Natural] -> Natural
testFoldr = foldr (\ _ x -> x) 0

```
