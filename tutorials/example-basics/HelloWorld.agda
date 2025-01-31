module HelloWorld where

open import Haskell.Prelude

--defining a type synonym
Entry = Int × List String


--defining a datatype
data Tree (a : Type) : Type where
    Leaf   : a → Tree a
    Branch : a → Tree a → Tree a → Tree a

--agda2hs pragmas
{-# COMPILE AGDA2HS Entry #-}

{-# COMPILE AGDA2HS Tree #-}
