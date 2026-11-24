module MayThrowMonad where

open import Haskell.Prelude
open import Haskell.Control.Exception

postulate
  oops : AssertionFailed
{-# COMPILE AGDA2HS oops #-}

boom : MayThrow AssertionFailed Nat
boom = throw oops
{-# COMPILE AGDA2HS boom #-}

okay : MayThrow AssertionFailed Nat
okay = return 1
{-# COMPILE AGDA2HS okay #-}

bindMayThrow' : MayThrow AssertionFailed Nat → MayThrow AssertionFailed Nat
bindMayThrow' m = m >>= λ x → return (x + 1)
{-# COMPILE AGDA2HS bindMayThrow' #-}

mapMayThrow : MayThrow AssertionFailed Nat → MayThrow AssertionFailed Nat
mapMayThrow = fmap (_+ 1)
{-# COMPILE AGDA2HS mapMayThrow #-}

doMayThrow : MayThrow AssertionFailed Nat
doMayThrow = do
  x <- okay
  y <- return 3
  return (x + y)
{-# COMPILE AGDA2HS doMayThrow #-}

seqMayThrow : MayThrow AssertionFailed Nat → MayThrow AssertionFailed Nat
seqMayThrow m = boom >> m
{-# COMPILE AGDA2HS seqMayThrow #-}
