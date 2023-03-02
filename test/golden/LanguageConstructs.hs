{-# LANGUAGE LambdaCase #-}
module LanguageConstructs where

oneTwoThree :: [Int]
oneTwoThree = [1, 2, 3]

exactlyTwo :: [a] -> Maybe (a, a)
exactlyTwo [x, y] = Just (x, y)
exactlyTwo _ = Nothing

ifThenElse :: Int -> String
ifThenElse n = if n >= 10 then "big" else "small"

maybeToList :: Maybe a -> [a]
maybeToList
  = \case
        Nothing -> []
        Just x -> [x]

mhead :: [a] -> Maybe a
mhead xs
  = case xs of
        [] -> Nothing
        x : _ -> Just x

plus5minus5 :: Int -> Int
plus5minus5 n
  = case n + 5 of
        m -> m - 5

enum₁ :: [Int]
enum₁ = [5 .. 10]

enum₂ :: [Integer]
enum₂ = [10, 20 .. 100]

enum₃ :: [Bool]
enum₃ = [False ..]

enum₄ :: [Ordering]
enum₄ = [LT, EQ ..]

underappliedEnum :: [Int] -> [[Int]]
underappliedEnum = map (enumFromTo 1)

