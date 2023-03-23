open import Haskell.Prelude

data Planet : Set where
  Mercury : Planet
  Venus   : Planet
  Earth   : Planet
  Mars    : Planet
  Jupiter : Planet
  Saturn  : Planet
  Uranus  : Planet
  Neptune : Planet
  Pluto   : Planet

{-# COMPILE AGDA2HS Planet #-}

postulate instance iPlanetEq : Eq Planet

{-# COMPILE AGDA2HS iPlanetEq #-}

data Optional (a : Set) : Set where
  Of    : a → Optional a
  Empty : Optional a

{-# COMPILE AGDA2HS Optional #-}

postulate instance iOptionalEq : ⦃ Eq a ⦄ → Eq (Optional a)

{-# COMPILE AGDA2HS iOptionalEq #-}

