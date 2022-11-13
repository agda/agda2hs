module Importer where

import Importee (Foo(MkFoo), Fooable(doTheFoo), foo, (!#))
import SecondImportee (anotherFoo)

bar :: Int
bar = foo

baz :: Int
baz = 21 !# 21

myFoo :: Foo
myFoo = MkFoo

myOtherFoo :: Foo
myOtherFoo = doTheFoo

otherBar :: Int
otherBar = anotherFoo

