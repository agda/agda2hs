-- The erased equality proof is nested inside the non-erased MkBox
-- constructor and forces the nested type argument a of MkBox, so this forced
-- pattern can only be found by recursing into the arguments of constructors
-- (see issue #494).
--
-- Note that MkBox does not use the type argument a, so agda2hs drops it and
-- the clause below would not actually be unsound if accepted. A case where the
-- forced argument is observable in the compiled Haskell type would need
-- existential (or indexed) datatypes, which agda2hs does not support yet.
-- This test therefore only guards the recursion itself.
open import Haskell.Prelude

data Box : Set₁ where
  MkBox : (a : Set) → @0 (a ≡ Nat) → Box
{-# COMPILE AGDA2HS Box #-}

bad : Box → Nat
bad (MkBox a refl) = zero
{-# COMPILE AGDA2HS bad #-}
