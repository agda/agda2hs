module WitnessedFlows where

data Range = MkRange Int Int

createRange :: Int -> Int -> Maybe Range
createRange low high
  = if low <= high then Just (MkRange low high) else Nothing

createRangeCase :: Int -> Int -> Maybe Range
createRangeCase low high
  = case low <= high of
        True -> Just (MkRange low high)
        False -> Nothing

