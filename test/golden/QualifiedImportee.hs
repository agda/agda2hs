module QualifiedImportee where

foo :: Int
foo = 43

(!#) :: Int -> Int -> Int
x !# y = x - y

data Foo = MkFoo

class Fooable a where
    doTheFoo :: a
    defaultFoo :: a
    {-# MINIMAL doTheFoo #-}
    defaultFoo = doTheFoo

instance Fooable Foo where
    doTheFoo = MkFoo

