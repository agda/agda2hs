-- Matching on a non-erased equality constraint refines the type parameters,
-- which introduces dot patterns in non-erased (type) positions. Since the
-- match itself is not erased, this is allowed (see issue #494).
open import Haskell.Prelude

subst : ∀ {a b : Type} ⦃ p : a ≡ b ⦄ → a → b
subst ⦃ refl ⦄ x = x
{-# COMPILE AGDA2HS subst #-}
