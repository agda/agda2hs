module Agda2Hs.Law.Int where

open import Haskell.Prim
open import Haskell.Prim.Int using ( int64 )

open import Agda2Hs.Law.Def

int64-injective : Injective int64
int64-injective refl = refl
