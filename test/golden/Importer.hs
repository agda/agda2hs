module Importer where

import Importee (Foo(MkFoo), Fooable(doTheFoo), foo, (!#))

bar :: Int
bar = foo

baz :: Int
baz = 21 !# 21

myFoo :: Foo
myFoo = MkFoo

myOtherFoo :: Foo
myOtherFoo = doTheFoo

