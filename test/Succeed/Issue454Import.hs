module Issue454Import
  (fExample, example2, exampleFun)
where

import Issue454Record (Example(Example, fun))

fExample :: a -> a
fExample a = a

example2 :: Example a
example2 = Example fExample

exampleFun :: Example a -> a -> a
exampleFun e = fun e

