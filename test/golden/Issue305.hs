module Issue305 where

class Class a where
    foo :: a -> a

instance Class Int where
    foo = (+ 1)

instance Class Bool where
    foo = not

test :: Int
test = foo 41

anotherTest :: Int
anotherTest = test

class Class a => Subclass a where
    bar :: a

instance Subclass Bool where
    bar = False

