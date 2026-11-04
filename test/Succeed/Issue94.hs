module Issue94
  (thing)
where

thing :: [a] -> [a]
thing xs = aux xs
  where
    aux :: [a] -> [a]
    aux xs = xs

