-- See issue #182.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

f : (m : Bool) → Bool
f m = g m greattruth
  where
  @0 greattruth : true ≡ true
  greattruth = refl
  g : (m : Bool) (@0 proof : true ≡ true) → Bool
  g m _ = m
{-# COMPILE AGDA2HS f #-}
