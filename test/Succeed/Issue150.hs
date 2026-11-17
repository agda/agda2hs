module Issue150
  (Tup(..), swap)
where

data Tup a b = MkTup{exl :: a, exr :: b}

swap :: Tup a b -> Tup b a
swap = \ x -> MkTup (exr x) (exl x)

