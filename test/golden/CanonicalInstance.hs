module CanonicalInstance where

class ClassA a where
  myA :: a

class (ClassA b) => ClassB b

myB :: (ClassB b) => b
myB = myA
