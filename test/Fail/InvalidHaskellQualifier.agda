module InvalidHaskellQualifier where

import Haskell.Prelude as pre

test : pre.Bool
test = pre.True
{-# COMPILE AGDA2HS test #-}
