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

postulate instance iPlanetShow : Show Planet

{-# COMPILE AGDA2HS iPlanetShow strategy:stock #-}

record Clazz (a : Set) : Set where
  field
    foo : a → Int
    bar : a → Bool

open Clazz ⦃...⦄ public

{-# COMPILE AGDA2HS Clazz class #-}

postulate instance iPlanetClazz : Clazz Planet

{-# COMPILE AGDA2HS iPlanetClazz strategy:anyclass #-}

data Optional (a : Set) : Set where
  Of    : a → Optional a
  Empty : Optional a

{-# COMPILE AGDA2HS Optional #-}

postulate instance iOptionalEq : ⦃ Eq a ⦄ → Eq (Optional a)

{-# COMPILE AGDA2HS iOptionalEq #-}

data Duo (a b : Set) : Set where
  MkDuo : (a × b) → Duo a b

{-# COMPILE AGDA2HS Duo newtype #-}

postulate instance iDuoEq : ⦃ Eq a ⦄ → ⦃ Eq b ⦄ → Eq (Duo a b)

{-# COMPILE AGDA2HS iDuoEq strategy:newtype #-}

