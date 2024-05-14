```haskell
module Where where

import Numeric.Natural (Natural)

bool2nat :: Bool -> Natural
bool2nat = error "postulate: Bool -> Natural"

ex1 :: Natural
ex1 = mult num + bool2nat True
  where
    num :: Natural
    num = 42
    mult :: Natural -> Natural
    mult = (* 100)

ex2 :: Natural
ex2 = mult num + bool2nat True
  where
    num :: Natural
    num = 42
    mult :: Natural -> Natural
    mult = (⊗ 100)
      where
        (⊗) :: Natural -> Natural -> Natural
        (⊗) = (*)

ex3 :: Natural -> Bool -> Natural
ex3 n b = mult num + bool2nat b
  where
    num :: Natural
    num = 42 + bool2nat b
    mult :: Natural -> Natural
    mult = (* n)

ex4 :: Bool -> Natural
ex4 b = mult 42
  where
    mult :: Natural -> Natural
    mult n = bump n (bool2nat b)
      where
        bump :: Natural -> Natural -> Natural
        bump x y = x * y + (n - bool2nat b)

ex4' :: Bool -> Natural
ex4' b = mult (bool2nat b)
  where
    mult :: Natural -> Natural
    mult n = bump n (bool2nat b)
      where
        bump :: Natural -> Natural -> Natural
        bump x y = go (x * y) (n - bool2nat b)
          where
            go :: Natural -> Natural -> Natural
            go z w = z + x + w + y + n + bool2nat b

ex5 :: [Natural] -> Natural
ex5 [] = zro
  where
    zro :: Natural
    zro = 0
ex5 (n : ns) = mult num + 1
  where
    num :: Natural
    num = 42 + ex5 ns
    mult :: Natural -> Natural
    mult = (* n)

ex6 :: [Natural] -> Bool -> Natural
ex6 [] b = zro
  where
    zro :: Natural
    zro = 0
ex6 (n : ns) b = mult [num, 1]
  where
    mult :: [Natural] -> Natural
    mult [] = bump 5 (bool2nat b)
      where
        bump :: Natural -> Natural -> Natural
        bump x y = x * y + n
    mult (m : ms) = bump n m
      where
        bump :: Natural -> Natural -> Natural
        bump x y = x * y + (m - n)
    num :: Natural
    num = 42 + ex6 ns True

ex7 :: Natural -> Natural
ex7 n₀ = go₁ n₀
  where
    go₁ :: Natural -> Natural
    go₁ n₁ = go₂ (n₀ + n₁)
      where
        go₂ :: Natural -> Natural
        go₂ n₂ = n₀ + n₁ + n₂

ex7' :: Natural -> Natural
ex7' n₀ = go₁ n₀
  where
    go₁ :: Natural -> Natural
    go₁ n₁ = go₂ (n₀ + n₁)
      where
        go₂ :: Natural -> Natural
        go₂ n₂ = go₃ (n₀ + n₁ + n₂)
          where
            go₃ :: Natural -> Natural
            go₃ n₃ = n₀ + n₁ + n₂ + n₃

ex8 :: Natural
ex8 = n₂
  where
    n₁ :: Natural
    n₁ = 1
    n₂ :: Natural
    n₂ = n₁ + 1

```
