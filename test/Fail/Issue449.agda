module Fail.Issue449 where

open import Haskell.Prelude

foo : Set → Int
foo _ = 42
{-# COMPILE AGDA2HS foo #-}

goo : ∀ {a : Set₁} → (a → Int) → Bool
goo _ = True
{-# COMPILE AGDA2HS goo #-}

test = goo foo
{-# COMPILE AGDA2HS test #-}
