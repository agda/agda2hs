module Issue454Record
  (Example(..))
where

data Example a = Example{fun :: a -> a}

