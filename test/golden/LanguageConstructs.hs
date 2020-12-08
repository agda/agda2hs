module LanguageConstructs where

oneTwoThree :: [Int]
oneTwoThree = [1, 2, 3]

exactlyTwo :: [a] -> Maybe (a, a)
exactlyTwo [x, y] = Just (x, y)
exactlyTwo _ = Nothing

ifThenElse :: Int -> String
ifThenElse n = if n >= 10 then "big" else "small"

