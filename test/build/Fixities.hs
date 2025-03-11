module Fixities where

leftAssoc :: Int -> [Int]
leftAssoc n
  = [2 * n + 1, 2 * (n + 1), 1 + n * 2, (1 + n) * 2, n + n + n,
     n + (n + n)]

rightAssoc :: [Int] -> [Int]
rightAssoc xs = xs ++ xs ++ ((xs ++ xs) ++ xs) ++ xs

nonAssoc :: Bool -> Bool
nonAssoc b = (b == b) == (b == b)

mixedAssoc :: Maybe Int -> (Int -> Maybe Int) -> Maybe Int
mixedAssoc m f = f =<< ((f =<< m) >>= f >>= f)

infixl 7 <+>
(<+>) :: Int -> Int -> Int
x <+> y = x + y

infixr 8 <->
(<->) :: Int -> Int -> Int
x <-> y = x - y

