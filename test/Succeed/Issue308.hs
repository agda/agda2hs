module Issue308
  (Class(..), tester)
where

class Class a where
    foo :: a -> a

instance Class Int where
    foo = (+ 1)

tester :: Int
tester = foo 41

