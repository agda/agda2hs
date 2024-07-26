{-# LANGUAGE UnboxedTuples, TupleSections #-}
module CustomTuples where

test :: (Int, Int) -> Int
test xy = fst xy + snd xy

foo ::
    (# Int, Int, Bool #) ->
      (# Int, Bool, Bool #) -> (# Int, Char, Bool #)
foo (# a, b, c #) (# x, y, z #)
  = (# a + b + x, 'x', or [c, y, z] #)

bare :: Int -> Char -> Bool -> (# Int, Char, Bool #)
bare = (# ,, #)

section :: a -> Bool -> (# Int, a, Bool #)
section = (# 42, , #)

bar :: () -> ()
bar () = ()

baz :: (Int) -> (Int)
baz (x) = (42)

