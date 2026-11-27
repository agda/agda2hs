module DoubleNumOrd where

open import Haskell.Prelude

-- Regression tests for https://github.com/agda/agda2hs/issues/500.
-- The `Double` definitions of `negate`, `abs`, `signum`, `max` and `min` should
-- agree with GHC's Prelude on signed zeros and NaN. Each of the following
-- equations holds by computation on the Agda side.

pzero : Double
pzero = 0.0

nzero : Double
nzero = -0.0

nan : Double
nan = primFloatDiv 0.0 0.0

negate-pzero : primFloatIsNegativeZero (negate pzero) ≡ True
negate-pzero = refl

abs-nzero : primFloatIsNegativeZero (abs nzero) ≡ False
abs-nzero = refl

signum-nan : primFloatIsNaN (signum nan) ≡ True
signum-nan = refl

signum-nzero : primFloatIsNegativeZero (signum nzero) ≡ True
signum-nzero = refl

max-zeros : primFloatIsNegativeZero (max pzero nzero) ≡ True
max-zeros = refl

min-zeros : primFloatIsNegativeZero (min pzero nzero) ≡ False
min-zeros = refl

max-nan : primFloatIsNaN (max nan 1.0) ≡ True
max-nan = refl

min-nan : primFloatIsNaN (min nan 1.0) ≡ False
min-nan = refl

doubleCases : Double → Double → Double → List Double
doubleCases z nz n = negate z ∷ abs nz ∷ signum n ∷ max z nz ∷ min n 1.0 ∷ []
{-# COMPILE AGDA2HS doubleCases #-}
