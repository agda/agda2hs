module Issue90 where

open import Haskell.Prelude

good : Nat
good = bar
  where
    foo : Nat
    foo = 42

    bar : Nat
    bar = foo
{-# COMPILE AGDA2HS good #-}

bad : Nat
bad = bar
  where
    bar : Nat
    foo : Nat
    bar = foo
    foo = 42
{-# COMPILE AGDA2HS bad #-}

good2 : Nat
good2 = bar
  where
    foo : Nat
    foo = 42 + x
      where
        x : Nat
        x = 1
    bar : Nat
    bar = foo + x
      where
        x : Nat
        x = 2
{-# COMPILE AGDA2HS good2 #-}

bad2 : Nat
bad2 = bar
  where
    bar : Nat
    foo : Nat
    foo = 42 + x
      where
        x : Nat
        x = 1
    bar = foo + x
      where
        x : Nat
        x = 2
{-# COMPILE AGDA2HS bad2 #-}

test : Bool → Nat
test true = bar
  where
    foo : Nat
    foo = 42 + ted
      where
        nes : Nat
        nes = 1
        ted : Nat
        ted = nes + 1

    bar : Nat
    bar = foo
test false = bar
  where
    bar : Nat
    foo : Nat
    foo = 42 + ted
      where
        ted : Nat
        nes : Nat
        nes = 1
        ted = nes + 1
    bar = foo
{-# COMPILE AGDA2HS test #-}

