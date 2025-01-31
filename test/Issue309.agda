module Issue309 where

open import Haskell.Prim using (Type)

private variable @0 a : Type

Ap : (p : @0 a → Type) → @0 a → Type
Ap p x = p x
{-# COMPILE AGDA2HS Ap #-}
