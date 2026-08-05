module PredNat where

open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Nat
open import Haskell.Extra.Refinement
open import Haskell.Law.Eq
open import Haskell.Law.Eq.Instances

-- The predecessor of a nonzero natural number.
predNat' : (n : Nat) → @0 (n ≡ 0 → ⊥) → Nat
predNat' n neq = predNat n neq .value

{-# COMPILE AGDA2HS predNat' #-}

-- A recursor for natural numbers, as suggested in issue #385.
recNat : (a : @0 Nat → Set)
       → (z : a 0)
       → (s : (m : Nat) → a m → a (suc m))
       → (n : Nat) → a n
recNat a z s n = ifDec (n ≟ 0)
  (λ where {{refl}} → z)
  (λ {{n≠0}} →
    case predNat n n≠0 of λ where
      (m ⟨ refl ⟩) → s m (recNat a z s m))

{-# COMPILE AGDA2HS recNat #-}
