module Issue145 where

open import Haskell.Prelude
open import Haskell.Prim.Strict

-- ** PASS

module _ {a : Set} where
  it : a → a
  it x = x
  {-# COMPILE AGDA2HS it #-}

it' : ⦃ Monoid a ⦄ → a → a
it' x = x
{-# COMPILE AGDA2HS it' #-}

data Ok' {ℓ} (a : Set ℓ) : Set ℓ where
  Thing' : Strict a → Ok' a
{-# COMPILE AGDA2HS Ok' #-}

-- ** FAIL

data Ok {a : Set} : Set where
  Thing : a → Ok
{-# COMPILE AGDA2HS Ok #-}

test : Ok
test = Thing "ok"
{-# COMPILE AGDA2HS test #-}
