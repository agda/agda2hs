
module Pragmas where

-- Check that Haskell code is parsed with the correct language pragmas
{-# FOREIGN AGDA2HS
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
#-}

{-# FOREIGN AGDA2HS
foo :: Bool -> a -> (a, Int)
foo = \ case
  False -> (, 0)
  True  -> (, 1)
#-}
