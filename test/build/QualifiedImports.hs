module QualifiedImports where

import qualified Importee (Foo(MkFoo), foo)
import QualifiedImportee ()
import qualified QualifiedImportee as Qually (Foo, Fooable(defaultFoo, doTheFoo), foo, (!#))

-- ** simple qualification

simpqualBar :: Int
simpqualBar = Importee.foo

simpfoo :: Importee.Foo
simpfoo = Importee.MkFoo

-- ** qualified imports

qualBar :: Int
qualBar = Qually.foo

qualBaz :: Int
qualBaz = (Qually.!#) 2 2

qualFooable :: Qually.Foo
qualFooable = Qually.doTheFoo

qualDefaultBar :: Qually.Foo
qualDefaultBar = Qually.defaultFoo

type Foo = Importee.Foo

