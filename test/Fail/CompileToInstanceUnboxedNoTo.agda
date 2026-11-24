open import Haskell.Prelude

record Wrap (a : Type) : Type where
  constructor wrap
  field unwrap : List a
open Wrap public
{-# COMPILE AGDA2HS Wrap unboxed #-}

instance
  iEqWrap : {{Eq a}} → Eq (Wrap a)
  iEqWrap {a} ._==_ = eqWrap
    where
      eqWrap : Wrap a → Wrap a → Bool
      eqWrap (wrap []) (wrap []) = True
      eqWrap (wrap (x ∷ xs)) (wrap (y ∷ ys)) = x == y && eqWrap (wrap xs) (wrap ys)
      eqWrap _ _ = False

-- The instance is compiled, but it is for an unboxed record, so it must also
-- have a `to` pragma pointing to the instance for the underlying type.
{-# COMPILE AGDA2HS iEqWrap #-}
