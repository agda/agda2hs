{-# OPTIONS --no-auto-inline #-}
module Where where

open import Haskell.Prelude

postulate
  bool2nat : Bool → Nat

-- no outer arguments
ex1 : Nat
ex1 = mult num + bool2nat true
  where
    num : Nat
    num = 42

    mult : Nat → Nat
    mult = _* 100

-- nested where
ex2 : Nat
ex2 = mult num + bool2nat true
  where
    num : Nat
    num = 42

    mult : Nat → Nat
    mult = _⊗ 100
      where
        _⊗_ = _*_

-- with outer arguments
ex3 : Nat → Bool → Nat
ex3 n b = mult num + bool2nat b
  where
    num = 42 + bool2nat b

    mult : Nat → Nat
    mult = _* n

-- nested where with outer arguments
ex4 : Bool → Nat
ex4 b = mult 42
  where
    mult : Nat → Nat
    mult n = bump n (bool2nat b)
      where
        bump : Nat → Nat → Nat
        bump x y = x * y + (n - bool2nat b)

ex4' : Bool → Nat
ex4' b = mult (bool2nat b)
  where
    mult : Nat → Nat
    mult n = bump n (bool2nat b)
      where
        bump : Nat → Nat → Nat
        bump x y = go (x * y) (n - bool2nat b)
          where
            go : Nat → Nat → Nat
            go z w = z + x + w + y + n + bool2nat b

-- with pattern matching and multiple clauses
ex5 : List Nat → Nat
ex5 [] = zro
  where
    zro : Nat
    zro = 0
ex5 (n ∷ ns) = mult num + 1
  where
    num = 42 + ex5 ns

    mult : Nat → Nat
    mult = _* n

-- mix of patterns + inner multiple clauses + nested where
ex6 : List Nat → Bool → Nat
ex6 [] b = zro
  where
    zro : Nat
    zro = 0
ex6 (n ∷ ns) b = mult (num ∷ 1 ∷ [])
  where
    mult : List Nat → Nat
    mult [] = bump 5 (bool2nat b)
      where
        bump : Nat → Nat → Nat
        bump x y = x * y + n
    mult (m ∷ ms) = bump n m
      where
        bump : Nat → Nat → Nat
        bump x y = x * y + (m - n)

    num = 42 + ex6 ns true

ex7 : Nat → Nat
ex7 n₀ = go₁ n₀
  where
    go₁ : Nat → Nat
    go₁ n₁ = go₂ (n₀ + n₁)
      where
        go₂ : Nat → Nat
        go₂ n₂ = n₀ + n₁ + n₂

ex7' : Nat → Nat
ex7' n₀ = go₁ n₀
  where
    go₁ : Nat → Nat
    go₁ n₁ = go₂ (n₀ + n₁)
      where
        go₂ : Nat → Nat
        go₂ n₂ = go₃ (n₀ + n₁ + n₂)
          where
            go₃ : Nat → Nat
            go₃ n₃ = n₀ + n₁ + n₂ + n₃

ex8 : Nat
ex8 = n₂
  where
    n₁ : Nat
    n₁ = 1
    n₂ = n₁ + 1

{-# COMPILE AGDA2HS bool2nat #-}
{-# COMPILE AGDA2HS ex1 #-}
{-# COMPILE AGDA2HS ex2 #-}
{-# COMPILE AGDA2HS ex3 #-}
{-# COMPILE AGDA2HS ex4 #-}
{-# COMPILE AGDA2HS ex4' #-}
{-# COMPILE AGDA2HS ex5 #-}
{-# COMPILE AGDA2HS ex6 #-}
{-# COMPILE AGDA2HS ex7 #-}
{-# COMPILE AGDA2HS ex7' #-}
{-# COMPILE AGDA2HS ex8 #-}
