module Haskell.Prim.RealFrac where

open import Haskell.Prim

postulate
  properFraction : Float → Σ Int (λ _ → Float)
  truncate       : Float → Int
  round          : Float → Int
  ceiling        : Float → Int
  floor          : Float → Int

--------------------------------------------------
-- Arithmetic

