module CompileToDataConstructor where

open import Haskell.Prelude

-- The target datatype is an existing definition with a regular COMPILE pragma.
data Target : Set where
  MkTarget : Bool → Target
{-# COMPILE AGDA2HS Target #-}

-- The source datatype has a constructor with a different name, but it is
-- otherwise the same. Uses of `MkSource` are compiled to `MkTarget`, so the
-- generated Haskell code still compiles; agda2hs only warns that the names do
-- not match.
data Source : Set where
  MkSource : Bool → Source
{-# COMPILE AGDA2HS Source to Target #-}
