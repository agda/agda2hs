module EqualityConstraint where

open import Haskell.Prelude

postulate
  myFunc : ⦃ p : a ≡ b ⦄ → c

{-# COMPILE AGDA2HS myFunc #-}
