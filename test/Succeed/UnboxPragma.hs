module UnboxPragma where

sort1 :: [Int] -> [Int]
sort1 xs = xs

sort2 :: [Int] -> [Int]
sort2 xs = xs

sort3 :: [Int] -> [Int]
sort3 xs = xs

sortAll :: [[Int]]
sortAll = map (\ r -> r) (map (\ xs -> xs) [[1, 2], [3]])

type Scope name = Int

emptyScope :: Scope name
emptyScope = 0

