module Haskell.Law.Extensionality where

open import Haskell.Prim

-------------------------------------------------------------------------------
-- Axiom: Functions are equal if they agree on all arguments.
--
-- This axiom is sometimes needed for proving properties of higher-order
-- functions, such as 'filter', 'fmap', or '(>>=)'.

postulate
  ext : ∀ {f g : a → b} → (∀ x → f x ≡ g x) → f ≡ g
