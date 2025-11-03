module Fail.ErasedPatternLambda where

open import Haskell.Prelude

Scope = List Bool

data Telescope (@0 α : Scope) : @0 Scope → Type where
  ExtendTel : ∀ {@0 x β} → Bool → Telescope (x ∷ α) β  → Telescope α (x ∷ β)
{-# COMPILE AGDA2HS Telescope #-}

caseTelBind : ∀ {@0 x α β} (tel : Telescope α (x ∷ β))
            → ((a : Bool) (rest : Telescope (x ∷ α) β) → @0 tel ≡ ExtendTel a rest → d)
            → d
caseTelBind (ExtendTel a tel) f = f a tel refl

{-# COMPILE AGDA2HS caseTelBind #-}

checkSubst : ∀ {@0 x α β} (t : Telescope α (x ∷ β)) → Bool
checkSubst t = caseTelBind t λ ty rest → λ where refl → True
{-# COMPILE AGDA2HS checkSubst #-}
