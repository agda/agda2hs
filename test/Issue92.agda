open import Haskell.Prelude

postulate Something : Type
postulate something : Something

module _ {a : Type} where
  foo : a → a
  foo x = bar {something}
    where
      bar : @0 {Something} → a
      bar {eq} = baz
        where
          baz : a
          baz = x
{-# COMPILE AGDA2HS foo #-}
