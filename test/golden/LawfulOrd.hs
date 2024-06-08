module LawfulOrd where

data Ordered a
  = Gt a a
  | Lt a a
  | E a a

order :: (Ord a) => a -> a -> Ordered a
order left right
  | left < right = Lt left right
  | left == right = E left right
  | otherwise = Gt left right
