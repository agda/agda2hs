module MatchOnMayThrow where

open import Haskell.Prelude
open import Haskell.Control.Exception

-- The constructors of the MayThrow monad are erased when compiling to
-- Haskell, so they cannot be pattern matched.
bad : MayThrow AssertionFailed Nat → Bool
bad (ok _) = True
bad (throw _) = False

{-# COMPILE AGDA2HS bad #-}
