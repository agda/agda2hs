open import Haskell.Prelude

module Issue353 where
-- Calling functions between local anonymous modules removed arguments

module FooBar (a : Bool) where
    hello : Bool
    hello = a
    {-# COMPILE AGDA2HS hello #-}

module Foo (a : Bool) where
    -- If the name of the current module is a prefix of the called module
    -- they would be interpreted as the same module
    world : Bool
    world = FooBar.hello a
    {-# COMPILE AGDA2HS world #-}

    open FooBar a
    world2 : Bool
    world2 = hello
    {-# COMPILE AGDA2HS world2 #-}

module _ (a : Bool) (b : Int) where
    foo : Bool
    foo = not a
    {-# COMPILE AGDA2HS foo #-}

module _ (b : Bool) where

    bar : Bool
    bar = foo True 0
    {-# COMPILE AGDA2HS bar #-}

    baz : Bool
    baz = bar
    {-# COMPILE AGDA2HS baz #-}

    callFromNested : Bool
    callFromNested = nested
      where nested = bar
    {-# COMPILE AGDA2HS callFromNested #-}

-- The check is needed both for instance declarations and where-clauses
