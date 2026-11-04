module Issue454Import
  (fExample, example2)
where

import Issue454Record (Example(Example))

fExample :: a -> a
fExample a = a

example2 :: Example a
example2 = Example fExample

