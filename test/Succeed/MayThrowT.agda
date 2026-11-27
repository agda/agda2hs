module MayThrowT where

open import Haskell.Prelude
open import Haskell.Control.Exception

postulate
  oops : AssertionFailed
{-# COMPILE AGDA2HS oops #-}

-- The MayThrow monad transformer over IO.
pureT : MayThrowT AssertionFailed IO Nat
pureT = return 5
{-# COMPILE AGDA2HS pureT #-}

throwT' : MayThrowT AssertionFailed IO Nat
throwT' = throwT oops
{-# COMPILE AGDA2HS throwT' #-}

liftT : MayThrowT AssertionFailed IO Nat
liftT = liftMayThrowT (return 1)
{-# COMPILE AGDA2HS liftT #-}

mapT : MayThrowT AssertionFailed IO Nat → MayThrowT AssertionFailed IO Nat
mapT = fmap (_+ 1)
{-# COMPILE AGDA2HS mapT #-}

bindT : MayThrowT AssertionFailed IO Nat → MayThrowT AssertionFailed IO Nat
bindT m = m >>= λ x → return (x + 1)
{-# COMPILE AGDA2HS bindT #-}
