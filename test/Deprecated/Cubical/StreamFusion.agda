-- Deprecated: agda2hs does not currently support copattern definitions.
module Cubical.StreamFusion where

open import Haskell.Prelude

open import Agda.Primitive.Cubical
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

variable
  @0 i : Size

record Stream (a : Type) (@0 i : Size) : Type where
  coinductive; constructor _:>_
  field
    shead : a
    stail : ∀ {@0 j : Size< i} → Stream a j
open Stream public

{-# COMPILE AGDA2HS Stream #-}

smap  : (a → b) → Stream a i → Stream b i
smap  f s .shead = f (shead s)
smap  f s .stail = smap f (stail s)

{-# COMPILE AGDA2HS smap #-}

smap-fusion  : (f : a → b) (g : b → c) (s : Stream a i)
             → PathP (λ _ → Stream c i) (smap {i = i} g (smap {i = i} f s)) (smap {i = i} (λ x → g (f x)) s)
smap-fusion  f g s i .shead = g (f (shead s))
smap-fusion  f g s i .stail = smap-fusion f g (stail s) i
