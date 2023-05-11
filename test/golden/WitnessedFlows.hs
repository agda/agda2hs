module WitnessedFlows where

import Control.Monad (guard)

data Range = MkRange Int Int

createRange :: Int -> Int -> Maybe Range
createRange low high
  = if low <= high then Just (MkRange low high) else Nothing

createRange' :: Int -> Int -> Maybe Range
createRange' low high
  = if low <= high then
      if low <= high then Just (MkRange low high) else Nothing else
      Nothing

createRangeCase :: Int -> Int -> Maybe Range
createRangeCase low high
  = case low <= high of
        True -> Just (MkRange low high)
        False -> Nothing

createRangeGuardSeq :: Int -> Int -> Maybe Range
createRangeGuardSeq low high
  = do guard (low <= high)
       pure (MkRange low high)

createRangeGuardFmap :: Int -> Int -> Maybe Range
createRangeGuardFmap low high
  = MkRange low high <$ guard (low <= high)

