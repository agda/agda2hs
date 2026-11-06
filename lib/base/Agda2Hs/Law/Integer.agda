module Agda2Hs.Law.Integer where

open import Haskell.Prim

open import Agda2Hs.Law.Def

pos-injective : Injective pos
pos-injective refl = refl

neg-injective : Injective negsuc
neg-injective refl = refl
