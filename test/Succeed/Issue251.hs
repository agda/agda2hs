module Issue251
  (get, test)
where

get :: Int -> Int
get x = x

test :: Int
test = get 42

