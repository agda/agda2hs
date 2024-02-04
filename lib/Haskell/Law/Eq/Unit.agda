module Haskell.Law.Eq.Unit where

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Law.Eq.Def

instance
  iLawfulEqUnit : IsLawfulEq ⊤
  iLawfulEqUnit .isEquality tt tt = refl
