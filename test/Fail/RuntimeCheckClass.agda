module Fail.RuntimeCheckClass where

open import Haskell.Prelude

record Class : Set where
  field
    theField : Nat
open Class public
{-# COMPILE AGDA2HS Class class #-}

record NoClass : Set where
  field
    classFst : Nat
    classSnd : ⦃@0 _ : IsTrue (classFst > 0)⦄ → Nat
open NoClass public
{-# COMPILE AGDA2HS NoClass class #-}
