module Records where

import Numeric.Natural (Natural)

data Pair a b = MkPair{proj₁ :: a, proj₂ :: b}

data Wrap a = Wrap{unwrap :: a}

class MyMonoid a where
    mempty :: a
    mappend :: a -> a -> a

swap :: Pair a b -> Pair b a
swap (MkPair x y) = MkPair y x

swap₂ :: Wrap (Pair a b) -> Wrap (Pair b a)
swap₂ (Wrap p) = Wrap (MkPair (proj₂ p) (proj₁ p))

data User = User{name :: String, code :: Natural}
              deriving (Eq, Show)

