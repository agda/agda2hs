module Issue92 where

open import Haskell.Prelude

foo : a → a
foo {a} x = bar x
  where
    bar : a -> a
    bar y = baz
      where
        baz : a
        baz = bag x
          where
            bag : a -> a
            bag _ = y
foo {a} x = foobar x
  where
    foobar : a -> a
    foobar _ = x
{-# COMPILE AGDA2HS foo #-}
