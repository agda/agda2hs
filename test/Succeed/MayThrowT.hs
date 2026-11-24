module MayThrowT
  (oops, pureT, throwT', liftT, mapT, bindT)
where

import Control.Exception (AssertionFailed, throw)
import Numeric.Natural (Natural)

oops :: AssertionFailed
oops = error "postulate: AssertionFailed"

pureT :: IO Natural
pureT = return 5

throwT' :: IO Natural
throwT' = pure (throw oops)

liftT :: IO Natural
liftT = fmap id (return 1)

mapT :: IO Natural -> IO Natural
mapT = fmap (+ 1)

bindT :: IO Natural -> IO Natural
bindT m
  = do x <- m
       return (x + 1)

