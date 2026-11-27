module Haskell.Extra.Nat where

open import Haskell.Prelude
open import Haskell.Extra.Refinement

-- | The predecessor of a nonzero natural number, together with a proof
-- that the original number is its successor. Since pattern matching on
-- 'Nat' is not allowed in Haskell, this is provided as a primitive that
-- compiles to Haskell's 'pred'.
postulate
  predNat : (n : Nat) → @0 (n ≡ 0 → ⊥) → ∃ Nat λ m → n ≡ suc m
