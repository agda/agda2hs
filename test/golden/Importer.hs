module Importer where

import Importee (Foo(MkFoo), Fooable(doTheFoo), foo, (!#))
import qualified QualifiedImportee as Qually
       (Foo, Fooable(doTheFoo), foo, (!#))
import SecondImportee (anotherFoo)

bar :: Int
bar = foo

otherBar :: Int
otherBar = anotherFoo

thirdBar :: Int
thirdBar = Qually.foo

baz :: Int
baz = 21 !# 21

otherBaz :: Int
otherBaz = (Qually.!#) 2 2

myFoo :: Foo
myFoo = MkFoo

myOtherFoo :: Foo
myOtherFoo = doTheFoo

thirdFoo :: Qually.Foo
thirdFoo = Qually.doTheFoo

