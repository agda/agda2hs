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
        mult n = bump n (bool2nat b)
          where bump :: Integer -> Integer -> Integer
                bump x y = x * y + n - bool2nat b

ex4' :: Bool -> Integer
ex4' b = mult (bool2nat b)
  where mult :: Integer -> Integer
        mult n = bump n (bool2nat b)
          where bump :: Integer -> Integer -> Integer
                bump x y = go (x * y) (n - bool2nat b)
                  where go :: Integer -> Integer -> Integer
                        go z w = z + x + w + y + n + bool2nat b

ex5 :: [Integer] -> Integer
ex5 [] = zro
  where zro :: Integer
        zro = 0
ex5 (n : ns) = mult num + 1
  where num :: Integer
        num = 42 + ex5 ns
        mult :: Integer -> Integer
        mult = (* n)

ex6 :: [Integer] -> Bool -> Integer
ex6 [] b = zro
  where zro :: Integer
        zro = 0
ex6 (n : ns) b = mult (num : 1 : [])
  where mult :: [Integer] -> Integer
        mult [] = bump 5 (bool2nat b)
          where bump :: Integer -> Integer -> Integer
                bump x y = x * y + n
        mult (m : ms) = bump n m
          where bump :: Integer -> Integer -> Integer
                bump x y = x * y + m - n
        num :: Integer
        num = 42 + ex6 ns True

ex7 :: Integer -> Integer
ex7 n₀ = go₁ n₀
  where go₁ :: Integer -> Integer
        go₁ n₁ = go₂ (n₀ + n₁)
          where go₂ :: Integer -> Integer
                go₂ n₂ = n₀ + n₁ + n₂

ex7' :: Integer -> Integer
ex7' n₀ = go₁ n₀
  where go₁ :: Integer -> Integer
        go₁ n₁ = go₂ (n₀ + n₁)
          where go₂ :: Integer -> Integer
                go₂ n₂ = go₃ (n₀ + n₁ + n₂)
                  where go₃ :: Integer -> Integer
                        go₃ n₃ = n₀ + n₁ + n₂ + n₃

ex8 :: Integer
ex8 = n₂
  where n₁ :: Integer
        n₁ = 1
        n₂ :: Integer
        n₂ = n₁ + 1

