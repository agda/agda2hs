open import Haskell.Prelude

-- An unboxed record whose single non-erased field is a `Maybe` is compiled to
-- `Maybe a` in Haskell. An `Eq` instance for it is therefore compiled to the
-- existing instance for `Maybe`, so no duplicate instance is generated.
record Wrap (a : Type) : Type where
  constructor wrap
  field unwrap : Maybe a
open Wrap public
{-# COMPILE AGDA2HS Wrap unboxed #-}

instance
  iEqWrap : {{Eq a}} → Eq (Wrap a)
  iEqWrap ._==_ (wrap Nothing)  (wrap Nothing)  = True
  iEqWrap ._==_ (wrap (Just x)) (wrap (Just y)) = x == y
  iEqWrap ._==_ _               _               = False
{-# COMPILE AGDA2HS iEqWrap to iEqMaybe #-}

test : Bool
test = wrap xy == wrap zw
  where
    xy : Maybe Int
    xy = Just 1
    zw : Maybe Int
    zw = Just 2
{-# COMPILE AGDA2HS test #-}
