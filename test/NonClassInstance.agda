
open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement

instance
  iDecIsTrue : {b : Bool} → Dec (IsTrue b)
  iDecIsTrue {False} = False ⟨ (λ ()) ⟩
  iDecIsTrue {True}  = True  ⟨ IsTrue.itsTrue ⟩

{-# COMPILE AGDA2HS iDecIsTrue #-}
