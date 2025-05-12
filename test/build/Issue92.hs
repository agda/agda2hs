{-# LANGUAGE ScopedTypeVariables #-}
module Issue92 where

foo :: forall a . a -> a
foo x = bar
  where
    bar :: a
    bar = baz
      where
        baz :: a
        baz = x

