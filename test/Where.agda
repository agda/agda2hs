{-# OPTIONS --no-auto-inline #-}
module Where where

open import Haskell.Prelude hiding (x; b; n; m)

postulate
  bool2nat : Bool -> Nat
{-# COMPILE AGDA2HS bool2nat #-}

-- no outer arguments
ex1 : Nat
ex1 = mult num + bool2nat true
  where
    num = 42

    mult : Nat -> Nat
    mult = _* 100
{-# COMPILE AGDA2HS ex1 #-}

-- nested where
ex2 : Nat
ex2 = mult num + bool2nat true
  where
    num = 42

    mult : Nat -> Nat
    mult = _⊗ 100
      where
        _⊗_ = _*_
{-# COMPILE AGDA2HS ex2 #-}

-- with outer arguments
ex3 : Nat -> Bool -> Nat
ex3 n b = mult num + bool2nat b
  where
    num = 42 + bool2nat b

    mult : Nat -> Nat
    mult = _* n
{-# COMPILE AGDA2HS ex3 #-}

-- nested where with outer arguments
ex4 : Bool -> Nat
ex4 b = mult 42
  where
    mult : Nat -> Nat
    mult n = bump 5 (bool2nat b)
      where
        bump : Nat -> Nat -> Nat
        bump x y = x * y + n
{-# COMPILE AGDA2HS ex4 #-}
