module Fail.Issue223 where

data Void : Set where
{-# COMPILE AGDA2HS Void #-}

test : {a : Set} → Void → a
test ()
{-# COMPILE AGDA2HS test #-}
