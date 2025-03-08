module Fail.DerivingParseFailure where

open import Haskell.Prim using (Type)

record Example : Type where
{-# COMPILE AGDA2HS Example deriving !& #-}
-- {-# COMPILE AGDA2HS Example deriving Show via Foo #-}
-- {-# COMPILE AGDA2HS Example deriving (Show, Eq, Ord) class #-}
