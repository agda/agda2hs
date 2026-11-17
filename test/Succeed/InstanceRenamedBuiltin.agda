open import Haskell.Prelude
open import Agda.Builtin.Nat renaming (_==_ to eqNat)

-- The body of this instance is a renamed builtin (`eqNat` is
-- `Agda.Builtin.Nat._==_`), whose concrete name coincides with the name of the
-- class method `_==_`. This used to be mistaken for a default method.
instance
  iEqNat' : Eq Nat
  iEqNat' ._==_ = eqNat

{-# COMPILE AGDA2HS iEqNat' to iEqNat #-}
