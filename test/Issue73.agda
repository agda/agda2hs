module Issue73 where

record ImplicitField (a : Set) : Set where
    field
        aField : a
        @0 {anImplicitField} : a
open ImplicitField public
{-# COMPILE AGDA2HS ImplicitField class #-}
