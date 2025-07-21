module RuntimeCheckUseCases where

open import Haskell.Prelude
open import Haskell.Extra.Dec

subtractFromGreater : (x y : Nat) ⦃@0 _ : IsFalse (x < y)⦄ → Nat
subtractFromGreater x y = x - y
{-# COMPILE AGDA2HS subtractFromGreater #-}

headOfNonEmpty : (xs : List Nat) ⦃@0 _ : NonEmpty xs ⦄ → Nat
headOfNonEmpty (x ∷ _) = x
{-# COMPILE AGDA2HS headOfNonEmpty #-}
