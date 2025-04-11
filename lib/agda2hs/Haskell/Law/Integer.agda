module Haskell.Law.Integer where

open import Haskell.Prim

open import Haskell.Law.Def

pos-injective : Injective pos
pos-injective refl = refl

neg-injective : Injective negsuc
neg-injective refl = refl
