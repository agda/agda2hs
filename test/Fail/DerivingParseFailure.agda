module Fail.DerivingParseFailure where

record Example : Set where
{-# COMPILE AGDA2HS Example deriving !& #-}
-- {-# COMPILE AGDA2HS Example deriving Show via Foo #-}
-- {-# COMPILE AGDA2HS Example deriving (Show, Eq, Ord) class #-}
