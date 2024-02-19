module Haskell.Law.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Law.Def

Just-injective : Injective (Just {a = a})
Just-injective refl = refl
