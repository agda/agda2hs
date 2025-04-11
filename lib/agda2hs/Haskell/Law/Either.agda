module Haskell.Law.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

open import Haskell.Law.Def

Left-injective : Injective (Left {a}{b})
Left-injective refl = refl

Right-injective : Injective (Right {a}{b})
Right-injective refl = refl
