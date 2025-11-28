open import Haskell.Prelude

data Planet : Type where
  Mercury : Planet
  Venus   : Planet
  Earth   : Planet
  Mars    : Planet
  Jupiter : Planet
  Saturn  : Planet
  Uranus  : Planet
  Neptune : Planet
  Pluto   : Planet

{-# COMPILE AGDA2HS Planet deriving ( Read ) #-}

instance
  iPlanetEq : Eq Planet
  iPlanetEq ._==_ Mercury Mercury = True
  iPlanetEq ._==_ Venus   Venus   = True
  iPlanetEq ._==_ Earth   Earth   = True
  iPlanetEq ._==_ Mars    Mars    = True
  iPlanetEq ._==_ Jupiter Jupiter = True
  iPlanetEq ._==_ Saturn  Saturn  = True
  iPlanetEq ._==_ Uranus  Uranus  = True
  iPlanetEq ._==_ Neptune Neptune = True
  iPlanetEq ._==_ Pluto   Pluto   = True
  iPlanetEq ._==_ _       _       = False

{-# COMPILE AGDA2HS iPlanetEq derive #-}

postulate instance iPlanetOrd : Ord Planet

{-# COMPILE AGDA2HS iPlanetOrd #-}

postulate instance iPlanetShow : Show Planet

{-# COMPILE AGDA2HS iPlanetShow derive stock #-}

record Clazz (a : Type) : Type where
  field
    foo : a → Int
    bar : a → Bool

open Clazz ⦃...⦄ public

{-# COMPILE AGDA2HS Clazz class #-}

postulate instance iPlanetClazz : Clazz Planet

{-# COMPILE AGDA2HS iPlanetClazz derive anyclass #-}

data Optional (a : Type) : Type where
  Of    : a → Optional a
  Empty : Optional a

{-# COMPILE AGDA2HS Optional #-}

postulate instance iOptionalEq : ⦃ Eq a ⦄ → Eq (Optional a)

{-# COMPILE AGDA2HS iOptionalEq #-}

data Duo (a b : Type) : Type where
  MkDuo : (a × b) → Duo a b

{-# COMPILE AGDA2HS Duo newtype #-}

instance
  iDuoEq : ⦃ Eq a ⦄ → ⦃ Eq b ⦄ → Eq (Duo a b)
  iDuoEq ._==_ (MkDuo d1) (MkDuo d2) = fst d1 == fst d2 && snd d1 == snd d2

{-# COMPILE AGDA2HS iDuoEq derive newtype #-}

