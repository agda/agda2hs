{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Pragmas where

foo :: Bool -> a -> (a, Int)
foo = \ case
  False -> (, 0)
  True  -> (, 1)

