open import Haskell.Prelude

foo : Int
foo = 42
{-# COMPILE AGDA2HS foo #-}

_!#_ : Int → Int → Int
x !# y = x + y
{-# COMPILE AGDA2HS _!#_ #-}

data Foo : Set where
  MkFoo : Foo
{-# COMPILE AGDA2HS Foo #-}

-- ** base
record Fooable (a : Set) : Set where
  field doTheFoo defaultFoo : a
-- ** defaults
record DefaultFooable (a : Set) : Set where
  field doTheFoo : a

  defaultFoo : a
  defaultFoo = doTheFoo
-- ** export
open Fooable ⦃...⦄ public
{-# COMPILE AGDA2HS Fooable class DefaultFooable #-}
-- ** instances
instance
  FF : Fooable Foo
  FF = record {DefaultFooable (λ where .doTheFoo → MkFoo)}
    where open DefaultFooable
{-# COMPILE AGDA2HS FF #-}

open import SecondImportee public
