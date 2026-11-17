-- The erased equality proof is nested inside the non-erased MkBox
-- constructor. Matching it still refines the type parameters a and b, so this
-- must be rejected (see issue #494).
open import Haskell.Prelude

data Box (a b : Set) : Set₁ where
  MkBox : (x : a) → @0 (a ≡ b) → Box a b
{-# COMPILE AGDA2HS Box #-}

bad : ∀ {a b : Set} → Box a b → a → b
bad (MkBox x refl) y = y
{-# COMPILE AGDA2HS bad #-}
