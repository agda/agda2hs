module Issue73 where

open import Haskell.Prim using (Type)

record ImplicitField (a : Type) : Type where
    field
        aField : a
        @0 {anImplicitField} : a
open ImplicitField public
{-# COMPILE AGDA2HS ImplicitField class #-}
