module Where where

bool2nat :: Bool -> Integer
bool2nat = error "postulate: Bool -> Integer"

ex1 :: Integer
ex1 = mult num + bool2nat True
  where num :: Integer
        num = 42
        mult :: Integer -> Integer
        mult = (* 100)

ex2 :: Integer
ex2 = mult num + bool2nat True
  where num :: Integer
        num = 42
        mult :: Integer -> Integer
        mult = (⊗ 100)
          where (⊗) :: Integer -> Integer -> Integer
                (⊗) = (*)

ex3 :: Integer -> Bool -> Integer
ex3 n b = mult num + bool2nat b
  where num :: Integer
        num = 42 + bool2nat b
        mult :: Integer -> Integer
        mult = (* n)

ex4 :: Bool -> Integer
ex4 b = mult 42
  where mult :: Integer -> Integer
        mult n = bump 5 (bool2nat b)
          where bump :: Integer -> Integer -> Integer
                bump x y = x * y + n

