{-# OPTIONS --erase-record-parameters #-}

module _ where

open import Haskell.Prelude

record ClassA (a : Set) : Set where
  field
    myA : a

open ClassA ⦃ ... ⦄ public
{-# COMPILE AGDA2HS ClassA class #-}

record ClassB (b : Set) : Set where
  field
    overlap ⦃ super ⦄ : ClassA b
{-# COMPILE AGDA2HS ClassB class #-}

myB : {{ClassB b}} → b
myB = myA
{-# COMPILE AGDA2HS myB #-}
