module Records where

data Pair a b = MkPair{fst :: a, snd :: b}

class MyMonoid a where
    mempty :: a
    mappend :: a -> a -> a

