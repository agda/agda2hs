module Agda2Hs.Law.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Agda2Hs.Law.Def

Just-injective : Injective (Just {a = a})
Just-injective refl = refl
