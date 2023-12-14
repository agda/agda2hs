module Inlining where

open import Haskell.Prelude

record Wrap (a : Set) : Set where
  constructor Wrapped
  field
    unwrap : a
open Wrap public
{-# COMPILE AGDA2HS Wrap unboxed #-}

mapWrap : (f : a → b) → Wrap a → Wrap b
mapWrap f (Wrapped x) = Wrapped (f x)
{-# COMPILE AGDA2HS mapWrap inline #-}

mapWrap2 : (f : a → b → c) → Wrap a → Wrap b → Wrap c
mapWrap2 f (Wrapped x) (Wrapped y) = Wrapped (f x y)
{-# COMPILE AGDA2HS mapWrap2 inline #-}

test1 : Wrap Int → Wrap Int
test1 x = mapWrap (1 +_) x
{-# COMPILE AGDA2HS test1 #-}

test2 : Wrap Int → Wrap Int → Wrap Int
test2 x y = mapWrap2 _+_ x y
{-# COMPILE AGDA2HS test2 #-}

-- partial application of inline function
test3 : Wrap Int → Wrap Int → Wrap Int
test3 x = mapWrap2 _+_ x
{-# COMPILE AGDA2HS test3 #-}

test4 : Wrap Int → Wrap Int → Wrap Int
test4 = mapWrap2 _+_
{-# COMPILE AGDA2HS test4 #-}
