module QualifiedRecordProjections where

open import Haskell.Prim using (Type)

record Test (a : Type) : Type where
  no-eta-equality
  field
    one : a

{-# COMPILE AGDA2HS Test #-}

test : {a : Type} → Test a → a
test x = Test.one x
{-# COMPILE AGDA2HS test #-}
