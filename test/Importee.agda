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

record Fooable (a : Set) : Set where
  field
    doTheFoo : a
open Fooable {{...}} public

{-# COMPILE AGDA2HS Fooable class #-}

instance
  FF : Fooable Foo
  FF .doTheFoo = MkFoo

{-# COMPILE AGDA2HS FF #-}
