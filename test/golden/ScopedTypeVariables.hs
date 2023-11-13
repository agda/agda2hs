{-# LANGUAGE ScopedTypeVariables #-}
module ScopedTypeVariables where

foo :: forall a . Eq a => a -> Bool
foo x = it x == x
  where
    it :: a -> a
    it = const x

bar :: forall a b . a -> b -> (b -> b) -> b
bar x y f = baz y
  where
    baz :: b -> b
    baz z = f (f z)

data D = MakeD Bool

mybool :: Bool
mybool = False

