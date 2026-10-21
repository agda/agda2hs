module Issue460
  (prepend)
where

prepend :: Bool -> [Int] -> [Int]
prepend b xs = (if b then [1] else []) ++ xs

