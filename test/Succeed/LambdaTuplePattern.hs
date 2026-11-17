module LambdaTuplePattern
  (fmapPair)
where

fmapPair :: (a -> b) -> (c, a) -> (c, b)
fmapPair = \ f x -> (fst x, f (snd x))

