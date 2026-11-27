module Tuples
  (swap, TuplePos(..), t1, t2, t3, pair, test, test2, t4, t5)
where

import Numeric.Natural (Natural)

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

data TuplePos = Test (TuplePos, Bool)

t1 :: (Bool, Bool, Bool)
t1 = (True, False, True)

t2 :: ((Bool, Bool), Bool)
t2 = ((True, False), True)

t3 :: (Bool, (Bool, Bool))
t3 = (True, (False, True))

pair :: (Int, Int)
pair = (1, 2)

test :: Int
test = fst pair + snd pair

test2 :: Bool
test2
  = case t1 of
        (a, b, c) -> c

t4 :: (Natural, Bool)
t4 = (3, True)

t5 :: (a, b) -> a
t5 p
  = case p of
        (x, y) -> x

