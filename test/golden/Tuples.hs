module Tuples where

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

unit2unit :: () -> ()
unit2unit () = ()

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

