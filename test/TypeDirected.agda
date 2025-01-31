{-# OPTIONS --prop #-}
module TypeDirected where

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.Unit
open import Haskell.Prelude

data MyProp : Prop where
  true : MyProp

myconst : {a : Type} → MyProp → a → {y : a} → a
myconst p x = x

{-# COMPILE AGDA2HS myconst #-}

defTrue : Term → TC ⊤
defTrue hole = unify hole (quoteTerm True)

fn : {@(tactic defTrue) b : Bool} → Int
fn {False} = 0
fn {True } = 5

{-# COMPILE AGDA2HS fn #-}

test1 : Int
test1 = fn

{-# COMPILE AGDA2HS test1 #-}

test2 : Int
test2 = fn {False}

{-# COMPILE AGDA2HS test2 #-}

