module QualifiedImportee where

foo :: Int
foo = 43

(!#) :: Int -> Int -> Int
x !# y = x - y

data Foo = MkFoo

class Fooable a where
    doTheFoo :: a

instance Fooable Foo where
    doTheFoo = MkFoo

