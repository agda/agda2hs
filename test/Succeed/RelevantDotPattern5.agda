-- Same as RelevantDotPattern4, but for an instance definition. This
-- exercises the (separate) code path for instance clauses with projections.
open import Haskell.Prelude

record Cast (a b : Type) : Type where
  no-eta-equality
  field runCast : a → b
open Cast public

instance
  castEq : ∀ {a b : Type} ⦃ p : a ≡ b ⦄ → Cast a b
  castEq ⦃ refl ⦄ .runCast x = x

{-# COMPILE AGDA2HS Cast class #-}
{-# COMPILE AGDA2HS castEq #-}
