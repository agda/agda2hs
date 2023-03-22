open import Haskell.Prelude

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

variable
  @0 i : Size

record Stream (a : Set) (@0 i : Size) : Set where
  pattern; inductive; constructor _:>_
  field
    shead : a
    stail : ∀ {@0 j} → Stream a j
open Stream public

{-# COMPILE AGDA2HS Stream #-}

smap  : (a → b) → Stream a i → Stream b i
smap  f (x :> xs) = (f x) :> smap f xs

{-# COMPILE AGDA2HS smap #-}

smap-fusion  : (f : a → b) (g : b → c) (s : Stream a i)
             → PathP (λ _ → Stream c i) (smap {i = i} g (smap {i = i} f s)) (smap {i = i} (λ x → g (f x)) s)
smap-fusion  f g (hd :> tl) i = (g (f hd)) :> smap-fusion f g tl i
