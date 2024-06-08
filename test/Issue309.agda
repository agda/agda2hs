module Issue309 where

private variable @0 a : Set

Ap : (p : @0 a → Set) → @0 a → Set
Ap p x = p x
{-# COMPILE AGDA2HS Ap #-}
