module MayThrowMonad
  (oops, boom, okay, bindMayThrow', mapMayThrow, doMayThrow, seqMayThrow)
where

import Control.Exception (AssertionFailed, throw)
import Numeric.Natural (Natural)

oops :: AssertionFailed
oops = error "postulate: AssertionFailed"

boom :: Natural
boom = throw oops

okay :: Natural
okay = 1

bindMayThrow' :: Natural -> Natural
bindMayThrow' m = let x = m in seq x (x + 1)

mapMayThrow :: Natural -> Natural
mapMayThrow = (+ 1)

doMayThrow :: Natural
doMayThrow = let x = okay in seq x (let y = 3 in seq y (x + y))

seqMayThrow :: Natural -> Natural
seqMayThrow m = seq boom m

