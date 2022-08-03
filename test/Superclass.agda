{-# OPTIONS --erase-record-parameters #-}
open import Haskell.Prelude

record Super (a : Set) : Set where
  field
    myFun : a → a
open Super {{...}}
{-# COMPILE AGDA2HS Super class #-}

record Sub (a : Set) : Set where
  field
    overlap {{super}} : Super a
open Sub {{...}}
{-# COMPILE AGDA2HS Sub class #-}

foo : {{Sub a}} → a → a
foo = myFun ∘ myFun
{-# COMPILE AGDA2HS foo #-}

-- Trying if diamonds are fine
record Sub2 (a : Set) : Set where
  field
    overlap {{super}} : Super a
open Sub2 {{...}}
{-# COMPILE AGDA2HS Sub2 class #-}

record Subber (a : Set) : Set where
  field
    overlap {{super}} : Sub a
    overlap {{super2}} : Sub2 a
open Subber {{...}}
{-# COMPILE AGDA2HS Subber class #-}

bar : {{Subber a}} → a → a
bar = myFun ∘ id
{-# COMPILE AGDA2HS bar #-}

instance
  iSuperInt : Super Int
  iSuperInt .myFun = 1 +_
{-# COMPILE AGDA2HS iSuperInt #-}

instance
  iSubInt : Sub Int
  iSubInt = record{}
{-# COMPILE AGDA2HS iSubInt #-}

-- Defining a subclass of an existing class from Prelude

record DiscreteOrd (a : Set) : Set where
  field
    overlap {{super}} : Ord a
open DiscreteOrd {{...}}
{-# COMPILE AGDA2HS DiscreteOrd class #-}

instance
  iDiscreteOrdBool : DiscreteOrd Bool
  iDiscreteOrdBool = record {}
{-# COMPILE AGDA2HS iDiscreteOrdBool #-}

baz : {{DiscreteOrd a}} → a → Bool
baz x = x < x

usebaz : Bool
usebaz = baz True
{-# COMPILE AGDA2HS baz #-}
{-# COMPILE AGDA2HS usebaz #-}
