module Haskell.Law.Nat where

open import Haskell.Prim

open import Haskell.Law.Def

suc-injective : Injective suc
suc-injective refl = refl
