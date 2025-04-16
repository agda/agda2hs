module Haskell.Law.Int where

open import Haskell.Prim
open import Haskell.Prim.Int using ( int64 )

open import Haskell.Law.Def

int64-injective : Injective int64
int64-injective refl = refl 
