module EqualityConstraint where

open import Haskell.Prelude hiding (c)

postulate
  c : Type

{-# COMPILE AGDA2HS c #-}

postulate
  myFunc : {@0 a b : Type} → ⦃ @0 p : a ≡ b ⦄ → c

{-# COMPILE AGDA2HS myFunc #-}
