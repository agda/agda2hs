module WitnessedFlows where

import Control.Monad (guard)

data Range = MkRange Int Int

createRange :: Int -> Int -> Maybe Range
createRange low high =
  if low <= high then Just (MkRange low high) else Nothing

createRange' :: Int -> Int -> Maybe Range
createRange' low high =
  if (low <= high) && (low <= high) then Just (MkRange low high) else Nothing

createRangeCase :: Int -> Int -> Maybe Range
createRangeCase low high =
  if low <= high then Just (MkRange low high) else Nothing

createRangeGuardSeq :: Int -> Int -> Maybe Range
createRangeGuardSeq low high =
  do
    guard (low <= high)
    pure (MkRange low high)

createRangeGuardFmap :: Int -> Int -> Maybe Range
createRangeGuardFmap low high =
  MkRange low high <$ guard (low <= high)
