
open import Haskell.Prelude
open import Agda2Hs.Extra.Dec
open import Agda2Hs.Extra.Refinement

foo : (b : Bool) → {{Dec (IsTrue b)}} → Bool
foo _ {{b ⟨ _ ⟩}} = not b

{-# COMPILE AGDA2HS foo #-}

bar : Bool → Bool
bar b = foo b

{-# COMPILE AGDA2HS bar #-}
