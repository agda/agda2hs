module Issue373 where

class MyShow a where
  myshow :: a -> String

anothershow :: MyShow a => a -> String
anothershow = myshow

