module Haskell.Control.Exception where

open import Haskell.Prim

open import Agda2Hs.Extra.Dec
open import Agda2Hs.Extra.Refinement

assert : (@0 b : Type ℓ) → {{Dec b}} → (@0 {{b}} → a) → a
assert _ {{True  ⟨ p ⟩}} x = x {{p}}
assert _ {{False ⟨ _ ⟩}} x = oops
  where postulate oops : _
