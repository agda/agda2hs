
open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement

instance
  iDecIsTrue : {b : Bool} → Dec (IsTrue b)
  iDecIsTrue {False} = False ⟨ (λ ()) ⟩
  iDecIsTrue {True}  = True  ⟨ IsTrue.itsTrue ⟩

{-# COMPILE AGDA2HS iDecIsTrue #-}

foo : (b : Bool) → {{Dec (IsTrue b)}} → Bool
foo _ {{b ⟨ _ ⟩}} = not b

{-# COMPILE AGDA2HS foo #-}

bar : Bool → Bool
bar b = foo b

{-# COMPILE AGDA2HS bar #-}
