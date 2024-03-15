module Issue305 where

class Class a where
    foo :: a -> a

instance Class Int where
    foo = (+ 1)

test :: Int
test = foo 41

