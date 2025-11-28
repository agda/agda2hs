module Issue94 where

thing :: [a] -> [a]
thing xs = aux xs
  where
    aux :: [a] -> [a]
    aux xs = xs

