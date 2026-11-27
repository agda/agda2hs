module CompileToInstance
  (test)
where

test :: Bool
test = eqTest [1, 2] [1, 3]
  where
    eqTest :: [Int] -> [Int] -> Bool
    eqTest x y = x == y

